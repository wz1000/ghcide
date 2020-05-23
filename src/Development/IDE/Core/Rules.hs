-- Copyright (c) 2019 The DAML Authors. All rights reserved.
-- SPDX-License-Identifier: Apache-2.0

{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}
#include "ghc-api-version.h"

-- | A Shake implementation of the compiler service, built
--   using the "Shaker" abstraction layer for in-memory use.
--
module Development.IDE.Core.Rules(
    IdeState, GetDependencies(..), GetParsedModule(..), TransitiveDependencies(..),
    Priority(..), GhcSessionIO(..), GhcSessionFun(..),
    priorityTypeCheck,
    priorityGenerateCore,
    priorityFilesOfInterest,
    runAction, useE, useNoFileE, usesE,
    toIdeResult, defineNoFile,
    mainRule,
    getAtPoint,
    getDefinition,
    getTypeDefinition,
    highlightAtPoint,
    refsAtPoint,
    workspaceSymbols,
    getDependencies,
    getParsedModule,
    generateCore,
    ) where

import Fingerprint

import Data.Binary
import Util
import Data.Bifunctor (second)
import Control.Monad.Extra
import Control.Applicative
import Control.Monad.Trans.Class
import Control.Monad.Trans.Maybe
import Development.IDE.Core.Compile
import Development.IDE.Core.OfInterest
import Development.IDE.Types.Options
import Development.IDE.Spans.Documentation
import Development.IDE.Import.DependencyInformation
import Development.IDE.Import.FindImports
import           Development.IDE.Core.FileExists
import           Development.IDE.Core.FileStore        (getFileContents)
import           Development.IDE.Types.Diagnostics
import Development.IDE.Types.Location
import Development.IDE.GHC.Compat hiding (parseModule, typecheckModule)
import Development.IDE.GHC.Util
import Development.IDE.GHC.WithDynFlags
import Data.Either.Extra
import qualified Development.IDE.Types.Logger as L
import Data.Maybe
import           Data.Foldable
import qualified Data.IntMap.Strict as IntMap
import Data.IntMap.Strict (IntMap)
import Data.List
import qualified Data.Set                                 as Set
import qualified Data.HashSet                             as HS
import qualified Data.Text                                as T
import           Development.IDE.GHC.Error
import           Development.Shake                        hiding (Diagnostic)
import Development.IDE.Core.RuleTypes
import qualified Data.ByteString.Char8 as BS
import Development.IDE.Core.PositionMapping
import           Language.Haskell.LSP.Types

import qualified GHC.LanguageExtensions as LangExt
import HscTypes
import PackageConfig
import DynFlags (gopt_set, xopt)
import GHC.Generics(Generic)

import qualified Development.IDE.Spans.AtPoint as AtPoint
import Development.IDE.Core.Service
import Development.IDE.Core.Shake
import Development.Shake.Classes
import Control.Monad.Trans.Except (runExceptT)
import Data.ByteString (ByteString)
import Control.Concurrent.Async (concurrently)
import Control.Concurrent.Extra
import System.Time.Extra
import Control.Monad.Reader
import System.Directory ( getModificationTime )
import qualified System.Directory as Dir
import Control.Exception

import OccName
import qualified HieDb
import Data.Char

import Module (toInstalledUnitId)
import Packages

import System.IO


-- | This is useful for rules to convert rules that can only produce errors or
-- a result into the more general IdeResult type that supports producing
-- warnings while also producing a result.
toIdeResult :: Either [FileDiagnostic] v -> IdeResult v
toIdeResult = either (, Nothing) (([],) . Just)

-- | useE is useful to implement functions that aren’t rules but need shortcircuiting
-- e.g. getDefinition.
useE :: IdeRule k v => k -> NormalizedFilePath -> MaybeT IdeAction (v, PositionMapping)
useE k = MaybeT . useWithStaleFast k

useNoFileE :: IdeRule k v => IdeState -> k -> MaybeT IdeAction v
useNoFileE _ide k = fst <$> useE k emptyFilePath

usesE :: IdeRule k v => k -> [NormalizedFilePath] -> MaybeT Action [v]
usesE k = MaybeT . fmap sequence . uses k

defineNoFile :: IdeRule k v => (k -> Action v) -> Rules ()
defineNoFile f = define $ \k file -> do
    if file == emptyFilePath then do res <- f k; return ([], Just res) else
        fail $ "Rule " ++ show k ++ " should always be called with the empty string for a file"


------------------------------------------------------------
-- Exposed API

-- | Get all transitive file dependencies of a given module.
-- Does not include the file itself.
getDependencies :: NormalizedFilePath -> Action (Maybe [NormalizedFilePath])
getDependencies file = fmap transitiveModuleDeps <$> use GetDependencies file

-- | Try to get hover text for the name under point.
getAtPoint :: NormalizedFilePath -> Position -> IdeAction (Maybe (Maybe Range, [T.Text]))
getAtPoint file pos = fmap join $ runMaybeT $ do
  ide <- ask
  opts <- liftIO $ getIdeOptionsIO ide

  ((hf,_), mapping) <- useE GetHieFile file
  PDocMap dm <- lift $ maybe (PDocMap mempty) fst <$> (runMaybeT $ useE GetDocMap file)

  !pos' <- MaybeT (return $ fromCurrentPosition mapping pos)
  return $ AtPoint.atPoint opts hf dm pos'

lookupMod :: DynFlags -> IdeOptions -> ModuleName -> UnitId -> Bool -> MaybeT IdeAction Uri
lookupMod dflags opts mn uid isBoot
 | toInstalledUnitId uid == thisInstalledUnitId dflags = do
      f <- MaybeT $ locateModuleFile [importPaths dflags] (optExtensions opts) doesExist isBoot mn
      pure $ fromNormalizedUri . filePathToUri' $ f
  | otherwise = MaybeT $ do
    let mp = lookupPackage dflags uid
    case mp of
      Nothing -> pure Nothing
      Just (packageName -> PackageName p) ->
        case lookupModuleWithSuggestions dflags mn (Just p) of
          _ -> error "Goto def for package deps not implemented"
  where
    doesExist f = do
      e <- useWithStaleFast' GetFileExists f
      case stale e of
        Just r -> pure (fst r)
        Nothing -> liftIO $ do
          hPutStrLn stderr "WAITING FOR BARRIER *********************"
          r <- waitBarrier (uptoDate e)
          hPutStrLn stderr "BARRIER ENDED *********************"
          maybe (Dir.doesFileExist $ fromNormalizedFilePath f) pure r

-- | Goto Definition.
getDefinition :: NormalizedFilePath -> Position -> IdeAction (Maybe Location)
getDefinition file pos = runMaybeT $ do
    ide <- ask
    opts <- liftIO $ getIdeOptionsIO ide
    (hf,_) <- fst <$> useE GetHieFile file
    sess <- hscEnv . fst <$> useE GhcSession file
    hiedb <- lift $ hiedb <$> askShake
    -- liftIO $ L.logInfo (ideLogger ide) $ "Got HieFile ###########"
    AtPoint.gotoDefinition hiedb (lookupMod (hsc_dflags sess) opts) opts hf pos

getTypeDefinition :: NormalizedFilePath -> Position -> IdeAction (Maybe Location)
getTypeDefinition file pos = runMaybeT $ do
    ide <- ask
    opts <- liftIO $ getIdeOptionsIO ide
    (hf,_) <- fst <$> useE GetHieFile file
    sess <- hscEnv . fst <$> useE GhcSession file
    hiedb <- lift $ hiedb <$> askShake
    AtPoint.gotoTypeDefinition hiedb (lookupMod (hsc_dflags sess) opts) opts hf pos

highlightAtPoint :: NormalizedFilePath -> Position -> IdeAction (Maybe [DocumentHighlight])
highlightAtPoint file pos = runMaybeT $ do
    ((hf, PRefMap rf),mapping) <- useE GetHieFile file
    !pos' <- MaybeT (return $ fromCurrentPosition mapping pos)
    AtPoint.documentHighlight hf rf pos'

{-
reportDbState :: HieDb.HieDb -> MaybeT IdeAction ()
reportDbState hiedb = do
  ide <- ask
  imods <- liftIO $ map (HieDb.modInfoName . HieDb.hieModInfo) <$> HieDb.getAllIndexedMods hiedb
  mg <- fst <$> useE GetModuleGraph emptyFilePath
  let mods = nub $ map showableModuleName $ IntMap.elems $ depModuleNames mg
  liftIO $ L.logInfo (ideLogger ide) $ T.pack $ "Modules in graph but not indexed: " ++ show (map ShowableModuleName (mods \\ imods))
  pure ()
  -}

refsAtPoint :: NormalizedFilePath -> Position -> IdeAction (Maybe [Location])
refsAtPoint file pos = runMaybeT $ do
    hiedb <- lift $ hiedb <$> askShake
    -- _ <- lift $ runMaybeT $ reportDbState hiedb

    opts <- liftIO . getIdeOptionsIO =<< ask

    ((hf,PRefMap rf),mapping) <- useE GetHieFile file
    sess <- hscEnv . fst <$> useE GhcSession file
    !pos' <- MaybeT (return $ fromCurrentPosition mapping pos)
    AtPoint.referencesAtPoint hiedb (lookupMod (hsc_dflags sess) opts) hf rf pos'

workspaceSymbols :: T.Text -> IdeAction (Maybe [SymbolInformation])
workspaceSymbols query = runMaybeT $ do
  hiedb <- lift $ hiedb <$> askShake
  res <- liftIO $ HieDb.searchDef hiedb $ T.unpack query
  pure $ map AtPoint.defRowToSymbolInfo res

-- | Parse the contents of a daml file.
getParsedModule :: NormalizedFilePath -> Action (Maybe ParsedModule)
getParsedModule file = use GetParsedModule file

------------------------------------------------------------
-- Rules
-- These typically go from key to value and are oracles.

priorityTypeCheck :: Priority
priorityTypeCheck = Priority 0

priorityGenerateCore :: Priority
priorityGenerateCore = Priority (-1)

priorityFilesOfInterest :: Priority
priorityFilesOfInterest = Priority (-2)

-- | IMPORTANT FOR HLINT INTEGRATION:
-- We currently parse the module both with and without Opt_Haddock, and
-- return the one with Haddocks if it -- succeeds. However, this may not work
-- for hlint, and we might need to save the one without haddocks too.
-- See https://github.com/digital-asset/ghcide/pull/350#discussion_r370878197
-- and https://github.com/mpickering/ghcide/pull/22#issuecomment-625070490
getParsedModuleRule :: Rules ()
getParsedModuleRule = defineEarlyCutoff $ \GetParsedModule file -> do
    sess <- use_ GhcSession file
    let hsc = hscEnv sess
        -- After parsing the module remove all package imports referring to
        -- these packages as we have already dealt with what they map to.
        comp_pkgs = map (fst . mkImportDirs) (deps sess)
    opt <- getIdeOptions
    (_, contents) <- getFileContents file

    let dflags    = hsc_dflags hsc
        mainParse = getParsedModuleDefinition hsc opt comp_pkgs file contents

    -- Parse again (if necessary) to capture Haddock parse errors
    if gopt Opt_Haddock dflags
        then
            liftIO mainParse
        else do
            let hscHaddock = hsc{hsc_dflags = gopt_set dflags Opt_Haddock}
                haddockParse = getParsedModuleDefinition hscHaddock opt comp_pkgs file contents

            -- parse twice, with and without Haddocks, concurrently
            -- we cannot ignore Haddock parse errors because files of
            -- non-interest are always parsed with Haddocks
            -- If we can parse Haddocks, might as well use them
            --
            -- HLINT INTEGRATION: might need to save the other parsed module too
            ((fp,(diags,res)),(fph,(diagsh,resh))) <- liftIO $ concurrently mainParse haddockParse

            -- Merge haddock and regular diagnostics so we can always report haddock
            -- parse errors
            let diagsM = mergeDiagnostics diags diagsh
            case resh of
              Just _ -> pure (fph, (diagsM, resh))
              -- If we fail to parse haddocks, report the haddock diagnostics as well and
              -- return the non-haddock parse.
              -- This seems to be the correct behaviour because the Haddock flag is added
              -- by us and not the user, so our IDE shouldn't stop working because of it.
              Nothing  -> pure (fp, (diagsM, res))

getParsedModuleDefinition :: HscEnv -> IdeOptions -> [PackageName] -> NormalizedFilePath -> Maybe T.Text -> IO (Maybe ByteString, ([FileDiagnostic], Maybe ParsedModule))
getParsedModuleDefinition packageState opt comp_pkgs file contents = do
    (diag, res) <- parseModule opt packageState comp_pkgs (fromNormalizedFilePath file) (fmap textToStringBuffer contents)
    case res of
        Nothing -> pure (Nothing, (diag, Nothing))
        Just (contents, modu) -> do
            mbFingerprint <- if isNothing $ optShakeFiles opt
                then pure Nothing
                else Just . fingerprintToBS <$> fingerprintFromStringBuffer contents
            pure (mbFingerprint, (diag, Just modu))

getLocatedImportsRule :: Rules ()
getLocatedImportsRule =
    define $ \GetLocatedImports file -> do
        ms <- use_ GetModSummary file
        let imports = [(False, imp) | imp <- ms_textual_imps ms] ++ [(True, imp) | imp <- ms_srcimps ms]
        env_eq <- use_ GhcSession file
        let env = hscEnv env_eq
        let import_dirs = deps env_eq
        let dflags = addRelativeImport file (moduleName $ ms_mod ms) $ hsc_dflags env
        opt <- getIdeOptions
        (diags, imports') <- fmap unzip $ forM imports $ \(isSource, (mbPkgName, modName)) -> do
            diagOrImp <- locateModule dflags import_dirs (optExtensions opt) getFileExists modName mbPkgName isSource
            case diagOrImp of
                Left diags -> pure (diags, Left (modName, Nothing))
                Right (FileImport path) -> pure ([], Left (modName, Just path))
                Right (PackageImport pkgId) -> liftIO $ do
                    diagsOrPkgDeps <- computePackageDeps env pkgId
                    case diagsOrPkgDeps of
                        Left diags -> pure (diags, Right Nothing)
                        Right pkgIds -> pure ([], Right $ Just $ pkgId : pkgIds)
        let (moduleImports, pkgImports) = partitionEithers imports'
        case sequence pkgImports of
            Nothing -> pure (concat diags, Nothing)
            Just pkgImports -> pure (concat diags, Just (moduleImports, Set.fromList $ concat pkgImports))


-- | Given a target file path, construct the raw dependency results by following
-- imports recursively.
rawDependencyInformation :: [NormalizedFilePath] -> Action RawDependencyInformation
rawDependencyInformation fs = do
--    let initialArtifact = ArtifactsLocation f (ModLocation (Just $ fromNormalizedFilePath f) "" "") False
--        (initialId, initialMap) = getPathId initialArtifact emptyPathIdMap
    (_, rdi, ss) <- go fs
                    ((RawDependencyInformation IntMap.empty emptyPathIdMap IntMap.empty), IntMap.empty)
    let bm = IntMap.foldrWithKey (updateBootMap rdi) IntMap.empty ss
    return (rdi { rawBootMap = bm })
  where
    go :: [NormalizedFilePath] -> (RawDependencyInformation, IntMap ArtifactsLocation)
                               -> Action ([FilePathId], RawDependencyInformation, IntMap ArtifactsLocation)
    go [] (r, i) = pure ([], r, i)
    go (f:fs) a@(rawDepInfo, ss)
      | Just fid <- lookupPathToId (rawPathIdMap rawDepInfo) f = do
          (fids, r, bms) <- go fs a
          return (fid: fids, r, bms)
      | otherwise = do
          al <- modSummaryToArtifactsLocation f <$> use_ GetModSummary f
          importsOrErr <- use GetLocatedImports f
          let (fId, path_map) = getPathId al (rawPathIdMap rawDepInfo)
          let ss' = if isBootLocation al
                      then IntMap.insert (getFilePathId fId) al ss
                      else ss
          let rawDepInfo' = rawDepInfo { rawPathIdMap = path_map }
          case importsOrErr of
            Nothing -> do
            -- File doesn’t parse
              let rawDepInfo'' = insertImport fId (Left ModuleParseError) rawDepInfo'
              (fids, r1, r2) <- go fs (rawDepInfo'', ss)
              return (fId: fids, r1, r2)
            Just (modImports, pkgImports) -> do
              -- Get NFPs of the imports which have corresponding files
              let (no_file, with_file) = splitImports modImports
                  (mns, ls) = unzip with_file
              (fids, d', ss'') <- go (map artifactFilePath ls) (rawDepInfo', ss')
              let moduleImports' = map (,Nothing) no_file ++ zipEqual "raw_dep" mns (map Just fids)
              let rawDepInfo'' = insertImport fId (Right $ ModuleImports moduleImports' pkgImports) d'
              (fids, r1, r2) <- go fs (rawDepInfo'', ss'')
              return (fId : fids, r1, r2)

    splitImports :: [(Located ModuleName, Maybe ArtifactsLocation)]
                 -> ([Located (ModuleName)], [(Located ModuleName, ArtifactsLocation)])
    splitImports [] = ([], [])
    splitImports ((m, k):is) = let (ns, ls) = splitImports is
                               in case k of
                                    Nothing -> (m:ns, ls)
                                    Just a  -> (ns, (m, a):ls)

    updateBootMap pm boot_mod_id ArtifactsLocation{..} bm =
      if not artifactIsSource
        then
          let msource_mod_id = lookupPathToId (rawPathIdMap pm) (toNormalizedFilePath' $ dropBootSuffix artifactModLocation)
          in case msource_mod_id of
               Just source_mod_id -> insertBootId source_mod_id (FilePathId boot_mod_id) bm
               Nothing -> bm
        else bm

    dropBootSuffix :: ModLocation -> FilePath
    dropBootSuffix (ModLocation (Just hs_src) _ _) = reverse . drop (length @[] "-boot") . reverse $ hs_src
    dropBootSuffix _ = error "dropBootSuffix"

getDependencyInformationRule :: Rules ()
getDependencyInformationRule =
    define $ \GetDependencyInformation file -> do
       rawDepInfo <- rawDependencyInformation [file]
       pure ([], Just $ processDependencyInformation rawDepInfo)

reportImportCyclesRule :: Rules ()
reportImportCyclesRule =
    define $ \ReportImportCycles file -> fmap (\errs -> if null errs then ([], Just ()) else (errs, Nothing)) $ do
        DependencyInformation{..} <- use_ GetDependencyInformation file
        let fileId = pathToId depPathIdMap file
        case IntMap.lookup (getFilePathId fileId) depErrorNodes of
            Nothing -> pure []
            Just errs -> do
                let cycles = mapMaybe (cycleErrorInFile fileId) (toList errs)
                -- Convert cycles of files into cycles of module names
                forM cycles $ \(imp, files) -> do
                    modNames <- forM files $ \fileId -> do
                        let file = idToPath depPathIdMap fileId
                        getModuleName file
                    pure $ toDiag imp $ sort modNames
    where cycleErrorInFile f (PartOfCycle imp fs)
            | f `elem` fs = Just (imp, fs)
          cycleErrorInFile _ _ = Nothing
          toDiag imp mods = (fp , ShowDiag , ) $ Diagnostic
            { _range = (_range :: Location -> Range) loc
            , _severity = Just DsError
            , _source = Just "Import cycle detection"
            , _message = "Cyclic module dependency between " <> showCycle mods
            , _code = Nothing
            , _relatedInformation = Nothing
            , _tags = Nothing
            }
            where loc = srcSpanToLocation (getLoc imp)
                  fp = toNormalizedFilePath' $ srcSpanToFilename (getLoc imp)
          getModuleName file = do
           ms <- use_ GetModSummary file
           pure (moduleNameString . moduleName . ms_mod $ ms)
          showCycle mods  = T.intercalate ", " (map T.pack mods)

-- returns all transitive dependencies in topological order.
-- NOTE: result does not include the argument file.
getDependenciesRule :: Rules ()
getDependenciesRule =
    defineEarlyCutoff $ \GetDependencies file -> do
        depInfo <- use_ GetDependencyInformation file
        let allFiles = reachableModules depInfo
        _ <- uses_ ReportImportCycles allFiles
        opts <- getIdeOptions
        let mbFingerprints = map (fingerprintString . fromNormalizedFilePath) allFiles <$ optShakeFiles opts
        return (fingerprintToBS . fingerprintFingerprints <$> mbFingerprints, ([], transitiveDeps depInfo file))

getHieFileRule :: Rules ()
getHieFileRule =
    define $ \GetHieFile f -> do
      tcm <- use_ TypeCheck f
      hf <- case tmrHieFile tcm of
        Just hf -> pure ([],Just hf)
        Nothing -> do
          hsc  <- hscEnv <$> use_ GhcSession f
          ShakeExtras{hiedbChan} <- getShakeExtras
          liftIO $ generateAndWriteHieFile hsc hiedbChan (tmrModule tcm)
      let refmap = PRefMap . generateReferencesMap . getAsts . hie_asts
      pure $ fmap (\x -> (x,refmap x)) <$> hf

persistentHieFileRule :: Rules ()
persistentHieFileRule = addPersistentRule GetHieFile $ \file -> runMaybeT $ do
  nc <- asks ideNc
  db <- asks hiedb
  row <- MaybeT $ liftIO $ HieDb.lookupHieFileFromSource db $ fromNormalizedFilePath file
  let hie_loc = HieDb.hieModuleHieFile row
  liftIO $ hPutStrLn stderr "LOADING HIE FILE *********************"
  res <- liftIO $ try @SomeException $ loadHieFile (mkUpdater nc) hie_loc
  liftIO $ hPutStrLn stderr "LOADED HIE FILE *********************"
  let refmap = PRefMap . generateReferencesMap . getAsts . hie_asts
  MaybeT $ pure $ either (const Nothing) (\x -> Just (x,refmap x))  res

getDocMapRule :: Rules ()
getDocMapRule =
    define $ \GetDocMap file -> do
      hmi <- tmrModInfo <$> use_ TypeCheck file
      hsc <- hscEnv <$> use_ GhcSession file
      (_,(PRefMap rf)) <- use_ GetHieFile file

      deps <- fst <$> useWithStale GetDependencies file
      let tdeps = transitiveModuleDeps deps

-- When possible, rely on the haddocks embedded in our interface files
-- This creates problems on ghc-lib, see comment on 'getDocumentationTryGhc'
#if MIN_GHC_API_VERSION(8,6,0) && !defined(GHC_LIB)
      let parsedDeps = []
#else
      parsedDeps <- uses_ GetParsedModule tdeps
#endif

      ifaces <- uses_ GetModIface tdeps

      docMap <- liftIO $ evalGhcEnv hsc $ mkDocMap parsedDeps rf hmi (map hirModIface ifaces)
      return ([],Just $ PDocMap docMap)

-- Typechecks a module.
typeCheckRule :: Rules ()
typeCheckRule = define $ \TypeCheck file -> do
    pm <- use_ GetParsedModule file
    -- do not generate interface files as this rule is called
    -- for files of interest on every keystroke
    typeCheckRuleDefinition file pm SkipGenerationOfInterfaceFiles

getModuleGraphRule :: Rules ()
getModuleGraphRule = defineNoFile $ \GetModuleGraph -> do
  fs <- knownFiles
  rawDepInfo <- rawDependencyInformation (HS.toList fs)
  pure (processDependencyInformation rawDepInfo)


data GenerateInterfaceFiles
    = DoGenerateInterfaceFiles
    | SkipGenerationOfInterfaceFiles
    deriving (Show)

-- This is factored out so it can be directly called from the GetModIface
-- rule. Directly calling this rule means that on the initial load we can
-- garbage collect all the intermediate typechecked modules rather than
-- retain the information forever in the shake graph.
typeCheckRuleDefinition
    :: NormalizedFilePath     -- ^ Path to source file
    -> ParsedModule
    -> GenerateInterfaceFiles -- ^ Should generate .hi and .hie files ?
    -> Action (IdeResult TcModuleResult)
typeCheckRuleDefinition file pm generateArtifacts = do
  deps <- use_ GetDependencies file
  hsc  <- hscEnv <$> use_ GhcSession file
  -- Figure out whether we need TemplateHaskell or QuasiQuotes support
  let graph_needs_th_qq = needsTemplateHaskellOrQQ $ hsc_mod_graph hsc
      file_uses_th_qq   = uses_th_qq $ ms_hspp_opts (pm_mod_summary pm)
      any_uses_th_qq    = graph_needs_th_qq || file_uses_th_qq
  mirs      <- uses_ GetModIface (transitiveModuleDeps deps)
  bytecodes <- if any_uses_th_qq
    then -- If we use TH or QQ, we must obtain the bytecode
      fmap Just <$> uses_ GenerateByteCode (transitiveModuleDeps deps)
    else
      pure $ repeat Nothing

  setPriority priorityTypeCheck
  IdeOptions { optDefer = defer } <- getIdeOptions

  ShakeExtras{hiedbChan} <- getShakeExtras
  liftIO $ do
    res <- typecheckModule defer hsc (zipWith unpack mirs bytecodes) pm
    case res of
      (diags, Just (hsc,tcm)) | DoGenerateInterfaceFiles <- generateArtifacts -> do
        (diagsHie,hf) <- generateAndWriteHieFile hsc hiedbChan (tmrModule tcm)
        diagsHi  <- generateAndWriteHiFile hsc tcm
        return (diags <> diagsHi <> diagsHie, Just tcm{tmrHieFile=hf})
      (diags, res) -> return (diags, snd <$> res)
 where
  unpack HiFileResult{..} bc = (hirModSummary, (hirModIface, bc))
  uses_th_qq dflags =
    xopt LangExt.TemplateHaskell dflags || xopt LangExt.QuasiQuotes dflags


generateCore :: RunSimplifier -> NormalizedFilePath -> Action (IdeResult (SafeHaskellMode, CgGuts, ModDetails))
generateCore runSimplifier file = do
    deps <- use_ GetDependencies file
    (tm:tms) <- uses_ TypeCheck (file:transitiveModuleDeps deps)
    setPriority priorityGenerateCore
    packageState <- hscEnv <$> use_ GhcSession file
    liftIO $ compileModule runSimplifier packageState [(tmrModSummary x, tmrModInfo x) | x <- tms] tm

generateCoreRule :: Rules ()
generateCoreRule =
    define $ \GenerateCore -> generateCore (RunSimplifier True)

generateByteCodeRule :: Rules ()
generateByteCodeRule =
    define $ \GenerateByteCode file -> do
      deps <- use_ GetDependencies file
      (tm : tms) <- uses_ TypeCheck (file: transitiveModuleDeps deps)
      session <- hscEnv <$> use_ GhcSession file
      (_, guts, _) <- use_ GenerateCore file
      liftIO $ generateByteCode session [(tmrModSummary x, tmrModInfo x) | x <- tms] tm guts

-- A local rule type to get caching. We want to use newCache, but it has
-- thread killed exception issues, so we lift it to a full rule.
-- https://github.com/digital-asset/daml/pull/2808#issuecomment-529639547
type instance RuleResult GhcSessionIO = GhcSessionFun

data GhcSessionIO = GhcSessionIO deriving (Eq, Show, Typeable, Generic)
instance Hashable GhcSessionIO
instance NFData   GhcSessionIO
instance Binary   GhcSessionIO

newtype GhcSessionFun = GhcSessionFun (FilePath -> Action (IdeResult HscEnvEq))
instance Show GhcSessionFun where show _ = "GhcSessionFun"
instance NFData GhcSessionFun where rnf !_ = ()


loadGhcSession :: Rules ()
loadGhcSession = do
    defineNoFile $ \GhcSessionIO -> do
        opts <- getIdeOptions
        GhcSessionFun <$> optGhcSession opts
    -- This function should always be rerun because it consults a cache to
    -- see what HscEnv needs to be used for the file, which can change.
    -- However, it should also cut-off early if it's the same HscEnv as
    -- last time
    defineEarlyCutoff $ \GhcSession file -> do
        GhcSessionFun fun <- useNoFile_ GhcSessionIO
        alwaysRerun
        val <- fun $ fromNormalizedFilePath file

        -- TODO: What was this doing before?
--        opts <- getIdeOptions
        return (Just (BS.pack (show ( hash (snd val)))), val)

getHiFileRule :: Rules ()
getHiFileRule = defineEarlyCutoff $ \GetHiFile f -> do
  -- get all dependencies interface files, to check for freshness
  (deps,_) <- use_ GetLocatedImports f
  depHis  <- traverse (use GetHiFile) (mapMaybe (fmap artifactFilePath . snd) deps)

  ms <- use_ GetModSummary f
  let hiFile = toNormalizedFilePath'
             $ case ms_hsc_src ms of
                HsBootFile -> addBootSuffix (ml_hi_file $ ms_location ms)
                _ -> ml_hi_file $ ms_location ms

  IdeOptions{optInterfaceLoadingDiagnostics} <- getIdeOptions

  let mkInterfaceFilesGenerationDiag f intro
        | optInterfaceLoadingDiagnostics = mkDiag $ intro <> msg
        | otherwise = []
            where
                msg =
                    ": additional resource use while generating interface files in the background."
                mkDiag = pure
                       . ideErrorWithSource (Just "interface file loading") (Just DsInfo) f
                       . T.pack

  case sequence depHis of
    Nothing -> do
          let d = mkInterfaceFilesGenerationDiag f "Missing interface file dependencies"
          pure (Nothing, (d, Nothing))
    Just deps -> do
      gotHiFile <- getFileExists hiFile
      if not gotHiFile
        then do
          let d = mkInterfaceFilesGenerationDiag f "Missing interface file"
          pure (Nothing, (d, Nothing))
        else do
          hiVersion  <- use_ GetModificationTime hiFile
          modVersion <- use_ GetModificationTime f
          -- This used to not detect changes to unsaved files correct so it's
          -- important to use newerFileVersion
          let sourceModified = newerFileVersion modVersion hiVersion
          if sourceModified
            then do
              let d = mkInterfaceFilesGenerationDiag f "Stale interface file"
              pure (Nothing, (d, Nothing))
            else do
              session <- hscEnv <$> use_ GhcSession f
              r <- liftIO $ loadInterface session ms deps
              case r of
                Right iface -> do
                  let result = HiFileResult ms iface
                  return (Just (fingerprintToBS (getModuleHash iface)), ([], Just result))
                Left err -> do
                  let diag = ideErrorWithSource (Just "interface file loading") (Just DsError) f . T.pack $ err
                  return (Nothing, (pure diag, Nothing))

getModSummaryRule :: Rules ()
getModSummaryRule = define $ \GetModSummary f -> do
    dflags <- hsc_dflags . hscEnv <$> use_ GhcSession f
    (_, mFileContent) <- getFileContents f
    modS <- liftIO $ evalWithDynFlags dflags $ runExceptT $
        getModSummaryFromImports (fromNormalizedFilePath f) (textToStringBuffer <$> mFileContent)
    return $ either (,Nothing) (([], ) . Just) modS

getModIfaceRule :: Rules ()
getModIfaceRule = define $ \GetModIface f -> do
    fileOfInterest <- use_ IsFileOfInterest f
    let useHiFile =
          -- Never load interface files for files of interest
          not fileOfInterest
    mbHiFile <- if useHiFile then use GetHiFile f else return Nothing
    case mbHiFile of
        Just x ->
            return ([], Just x)
        Nothing
          | fileOfInterest -> do
            -- For files of interest only, create a Shake dependency on typecheck
            tmr <- use TypeCheck f
            return ([], extract tmr)
          | otherwise -> do
            -- the interface file does not exist or is out of date.
            -- Invoke typechecking directly to update it without incurring a dependency
            -- on the parsed module and the typecheck rules
            sess <- use_ GhcSession f
            let hsc = hscEnv sess
                -- After parsing the module remove all package imports referring to
                -- these packages as we have already dealt with what they map to.
                comp_pkgs = map (fst . mkImportDirs) (deps sess)
            opt <- getIdeOptions
            (_, contents) <- getFileContents f
            -- Embed --haddocks in the interface file
            hsc <- pure hsc{hsc_dflags = gopt_set (hsc_dflags hsc) Opt_Haddock}
            (_, (diags, mb_pm)) <- liftIO $ getParsedModuleDefinition hsc opt comp_pkgs f contents
            case mb_pm of
                Nothing -> return (diags, Nothing)
                Just pm -> do
                    (diags', tmr) <- typeCheckRuleDefinition f pm DoGenerateInterfaceFiles
                    -- Bang pattern is important to avoid leaking 'tmr'
                    let !res = extract tmr
                    return (diags <> diags', res)
    where
      extract Nothing = Nothing
      extract (Just tmr) =
        -- Bang patterns are important to force the inner fields
        Just $! HiFileResult (tmrModSummary tmr) (hm_iface $ tmrModInfo tmr)

isFileOfInterestRule :: Rules ()
isFileOfInterestRule = defineEarlyCutoff $ \IsFileOfInterest f -> do
    filesOfInterest <- getFilesOfInterest
    let res = f `elem` filesOfInterest
    return (Just (if res then "1" else ""), ([], Just res))

-- | A rule that wires per-file rules together
mainRule :: Rules ()
mainRule = do
    getParsedModuleRule
    getLocatedImportsRule
    getDependencyInformationRule
    reportImportCyclesRule
    getDependenciesRule
    typeCheckRule
    getHieFileRule
    getDocMapRule
    generateCoreRule
    generateByteCodeRule
    loadGhcSession
    getHiFileRule
    getModIfaceRule
    isFileOfInterestRule
    getModSummaryRule
    getModuleGraphRule
    persistentHieFileRule
