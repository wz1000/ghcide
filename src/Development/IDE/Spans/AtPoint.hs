-- Copyright (c) 2019 The DAML Authors. All rights reserved.
-- SPDX-License-Identifier: Apache-2.0

-- | Gives information about symbols at a given point in DAML files.
-- These are all pure functions that should execute quickly.
module Development.IDE.Spans.AtPoint (
    atPoint
  , gotoDefinition
  , gotoTypeDefinition
  , documentHighlight
  , referencesAtPoint
  , defRowToSymbolInfo
  ) where

import Debug.Trace
import           Development.IDE.GHC.Error
import Development.IDE.GHC.Orphans()
import Development.IDE.Types.Location
import           Language.Haskell.LSP.Types

-- DAML compiler and infrastructure
import Development.IDE.GHC.Compat
import Development.IDE.Types.Options
import Development.IDE.Spans.Common

-- GHC API imports
import FastString
import Name
import Outputable hiding ((<>))
import SrcLoc
import Module

import Control.Monad.Extra
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.Class
import Control.Monad.IO.Class
import           Data.Maybe
import           Data.List
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Array as A


import IfaceType
import Data.Either
import Data.List.Extra (dropEnd, nubOrd)

import HieDb (TypeRef(..), findTypeRefs, hieModuleHieFile, hieModInfo, lookupHieFile, HieDb, search,RefRow(..), findDef, DefRow(..), Res, (:.)(..),ModuleInfo(..))

type LookupModule m = FilePath -> ModuleName -> UnitId -> Bool -> MaybeT m Uri

rowToLoc :: Monad m => Res RefRow -> m (Maybe Location)
rowToLoc (row:.info) = do
  mfile <- case modInfoSrcFile info of
    Just f -> pure $ Just $ toUri f
    Nothing -> pure Nothing -- runMaybeT $ lookupModule (modInfoName info) (modInfoUnit info) (modInfoIsBoot info)
  pure $ flip Location range <$> mfile
  where
    range = Range start end
    start = Position (refSLine row - 1) (refSCol row -1)
    end = Position (refELine row - 1) (refECol row -1)

referencesAtPoint
  :: MonadIO m
  => HieDb
  -> LookupModule m
  -> HieFile
  -> RefMap
  -> Position
  -> MaybeT m [Location]
referencesAtPoint hiedb lookupModule hf rf pos = do
  let names = concat $ pointCommand hf pos (rights . M.keys . nodeIdentifiers . nodeInfo)
  locs <- forM names $ \name ->
    case nameModule_maybe name of
      Nothing ->
        pure $ maybe [] (map $ realSrcSpanToLocation . fst) $ M.lookup (Right name) rf
      Just mod -> do
         rows <- liftIO $ search hiedb (nameOccName name) (Just $ moduleName mod) (Just $ moduleUnitId mod)
         lift $ mapMaybeM rowToLoc rows
  typelocs <- forM names $ \name ->
    case nameModule_maybe name of
      Just mod | isTcClsNameSpace (occNameSpace $ nameOccName name) -> do
        refs <- liftIO $ findTypeRefs hiedb (nameOccName name) (moduleName mod) (moduleUnitId mod)
        pure $ mapMaybe typeRowToLoc refs
      _ -> pure []
  pure $ nubOrd $ concat locs ++ concat typelocs

typeRowToLoc :: Res TypeRef -> Maybe Location
typeRowToLoc (row:.info) = do
  file <- modInfoSrcFile info
  pure $ Location (toUri file) range
  where
    range = Range start end
    start = Position (typeRefSLine row - 1) (typeRefSCol row -1)
    end = Position (typeRefELine row - 1) (typeRefECol row -1)

documentHighlight
  :: Monad m
  => HieFile
  -> RefMap
  -> Position
  -> MaybeT m [DocumentHighlight]
documentHighlight hf rf pos = pure highlights
  where
    ns = concat $ pointCommand hf pos (rights . M.keys . nodeIdentifiers . nodeInfo)
    highlights = do
      n <- ns
      ref <- maybe [] id (M.lookup (Right n) rf)
      pure $ makeHighlight ref
    makeHighlight (sp,dets) =
      DocumentHighlight (realSrcSpanToRange sp) (Just $ highlightType $ identInfo dets)
    highlightType s =
      if any (isJust . getScopeFromContext) s
        then HkWrite
        else HkRead

gotoTypeDefinition
  :: MonadIO m
  => HieDb
  -> LookupModule m
  -> IdeOptions
  -> HieFile
  -> Maybe NormalizedFilePath
  -> Position
  -> MaybeT m [Location]
gotoTypeDefinition hiedb lookupModule ideOpts srcSpans mf pos
  = lift $ typeLocationsAtPoint hiedb lookupModule ideOpts pos srcSpans mf

-- | Locate the definition of the name at a given position.
gotoDefinition
  :: MonadIO m
  => HieDb
  -> LookupModule m
  -> IdeOptions
  -> HieFile
  -> Maybe NormalizedFilePath
  -> Position
  -> MaybeT m [Location]
gotoDefinition hiedb lookupModule ideOpts srcSpans mf pos =
  lift $ locationsAtPoint hiedb lookupModule ideOpts pos srcSpans mf

-- | Synopsis for the name at a given position.
atPoint
  :: MonadIO m
  => IdeOptions
  -> HieFile
  -> HieDb
  -> Position
  -> MaybeT m (Maybe Range, [T.Text])
atPoint IdeOptions{} hf hiedb pos = MaybeT $ fmap combineRes . sequence $ pointCommand hf pos hoverInfo
  where
    -- Hover info for values/data
    combineRes :: [(Maybe Range, [T.Text])] -> Maybe (Maybe Range, [T.Text])
    combineRes [] = Nothing
    combineRes xs@(x:_) = Just (fst x, concatMap snd xs)
    hoverInfo ast = do
      prettyNames <- liftIO $ mapM prettyName names
      pure (Just range, prettyNames ++ pTypes)
      where
        pTypes
          | length names == 1 = dropEnd 1 $ map wrapHaskell prettyTypes
          | otherwise = map wrapHaskell prettyTypes

        range = realSrcSpanToRange $ nodeSpan ast

        wrapHaskell x = "\n```haskell\n"<>x<>"\n```\n"
        info = nodeInfo ast
        names = M.assocs $ nodeIdentifiers info
        types = nodeType info

        docForName :: Name -> IO [T.Text]
        docForName name =
          case nameModule_maybe name of
            Nothing -> pure []
            Just mod -> do
              erow <- findDef hiedb (nameOccName name) (Just $ moduleName mod) (Just $ moduleUnitId mod)
              pure $ mapMaybe (\(d :. _) -> T.pack . spanDocToMarkdownForTest <$> defDoc d) erow

        prettyName (Right n, dets) = do
          docs <- docForName n
          pure $ T.unlines $
            wrapHaskell (showGhc n <> maybe "" (" :: " <> ) (prettyType <$> identType dets))
            : definedAt n
            : docs
        prettyName (Left m,_) = pure $ showGhc m

        prettyTypes = map (("_ :: "<>) . prettyType) types
        prettyType t = showGhc $ hieTypeToIface $ recoverFullType t arr

        definedAt name = "*Defined " <> T.pack (showSDocUnsafe $ pprNameDefnLoc name) <> "*"

        arr = hie_types hf

typeLocationsAtPoint
  :: forall m
   . MonadIO m
  => HieDb
  -> LookupModule m
  -> IdeOptions
  -> Position
  -> HieFile
  -> Maybe NormalizedFilePath
  -> m [Location]
typeLocationsAtPoint hiedb lookupModule _ideOptions pos ast trustFile =
  let ts = concat $ pointCommand ast pos getts
      getts x = nodeType ni  ++ (mapMaybe identType $ M.elems $ nodeIdentifiers ni)
        where ni = nodeInfo x
      arr = hie_types ast
      unfold = map (arr A.!)
      getTypes ts = flip concatMap (unfold ts) $ \case
        HTyVarTy n -> [n]
        HAppTy a (HieArgs xs) -> getTypes (a : map snd xs)
        HTyConApp tc (HieArgs xs) -> ifaceTyConName tc : getTypes (map snd xs)
        HForAllTy _ a -> getTypes [a]
        HFunTy a b -> getTypes [a,b]
        HQualTy a b -> getTypes [a,b]
        HCastTy a -> getTypes [a]
        _ -> []
    in fmap nubOrd $ concatMapM (fmap (maybe [] id) . nameToLocation hiedb lookupModule trustFile) (getTypes ts)

locationsAtPoint
  :: forall m
   . MonadIO m
  => HieDb
  -> LookupModule m
  -> IdeOptions
  -> Position
  -> HieFile
  -> Maybe NormalizedFilePath
  -> m [Location]
locationsAtPoint hiedb lookupModule _ideOptions pos ast trustFile =
  let ns = concat $ pointCommand ast pos (rights . M.keys . nodeIdentifiers . nodeInfo)
    in concatMapM (fmap (maybe [] id) . nameToLocation hiedb lookupModule trustFile) ns

-- | Given a 'Name' attempt to find the location where it is defined.
nameToLocation :: MonadIO m => HieDb -> LookupModule m -> Maybe NormalizedFilePath -> Name -> m (Maybe [Location])
nameToLocation hiedb lookupModule trustFile name = runMaybeT $
  case nameSrcSpan name of
    sp@(RealSrcSpan rsp)
      | Nothing <- trustFile
      , maybe True (stringToUnitId "fake_uid" ==) (moduleUnitId <$> nameModule_maybe name) ->
          MaybeT $ pure $ fmap pure $ srcSpanToLocation sp
      | Just fs <- trustFile
      , Nothing <- nameModule_maybe name ->
          MaybeT $ pure $ fmap pure $ Just  $ Location (fromNormalizedUri $ filePathToUri' fs) (realSrcSpanToRange rsp)
      | Just mod <- nameModule_maybe name -> do
          mrow <- liftIO $ lookupHieFile hiedb (moduleName mod) (moduleUnitId mod)
          fs <- case mrow of
            Nothing -> MaybeT $ pure Nothing
            Just row -> case modInfoSrcFile $ hieModInfo row of
              Nothing -> lookupModule (hieModuleHieFile row) (moduleName mod) (moduleUnitId mod) False
              Just fs -> pure $ toUri fs
          MaybeT $ pure $ fmap pure $ Just  $ Location fs (realSrcSpanToRange rsp)
    sp -> do
      guard (sp /= wiredInSrcSpan)
      traceM $ "NAME TO LOC ******************" ++ show (trustFile)
      -- This case usually arises when the definition is in an external package.
      -- In this case the interface files contain garbage source spans
      -- so we instead read the .hie files to get useful source spans.
      mod <- MaybeT $ return $ nameModule_maybe name
      traceM $ "NAME TO LOC ****************** module -- "
      erow <- liftIO $ findDef hiedb (nameOccName name) (Just $ moduleName mod) (Just $ moduleUnitId mod)
      traceM $ "NAME TO LOC ****************** module -- findDef " ++ show (length erow)
      case erow of
        [] -> MaybeT $ pure Nothing
        xs -> lift $ mapMaybeM (runMaybeT . defRowToLocation lookupModule) xs

defRowToLocation :: Monad m => LookupModule m -> Res DefRow -> MaybeT m Location
defRowToLocation lookupModule (row:.info) = do
  let start = Position (defSLine row - 1) (defSCol row - 1)
      end   = Position (defELine row - 1) (defECol row - 1)
      range = Range start end
  traceM $ "DEFROW TO LOC ******************" ++ show (range, modInfoSrcFile info)
  file <- case modInfoSrcFile info of
    Just src -> pure $ toUri src
    Nothing -> lookupModule (defSrc row) (modInfoName info) (modInfoUnit info) (modInfoIsBoot info)
  pure $ Location file range

toUri :: FilePath -> Uri
toUri = fromNormalizedUri . filePathToUri' . toNormalizedFilePath'

defRowToSymbolInfo :: Res DefRow -> Maybe SymbolInformation
defRowToSymbolInfo (DefRow{..}:.(modInfoSrcFile -> Just srcFile))
  = Just $ SymbolInformation (showGhc defNameOcc) kind Nothing loc Nothing
  where
    kind
      | isVarOcc defNameOcc = SkVariable
      | isDataOcc defNameOcc = SkConstructor
      | isTcOcc defNameOcc = SkStruct
      | otherwise = SkUnknown 1
    loc   = Location file range
    file  = fromNormalizedUri . filePathToUri' . toNormalizedFilePath' $ srcFile
    range = Range start end
    start = Position (defSLine - 1) (defSCol - 1)
    end   = Position (defELine - 1) (defECol - 1)
defRowToSymbolInfo _ = Nothing

pointCommand :: HieFile -> Position -> (HieAST TypeIndex -> a) -> [a]
pointCommand hf pos k =
    catMaybes $ M.elems $ flip M.mapWithKey (getAsts $ hie_asts hf) $ \fs ast ->
      case selectSmallestContaining (sp fs) ast of
        Nothing -> Nothing
        Just ast' -> Just $ k ast'
 where
   sloc fs = mkRealSrcLoc fs (line+1) (cha+1)
   sp fs = mkRealSrcSpan (sloc fs) (sloc fs)
   line = _line pos
   cha = _character pos


