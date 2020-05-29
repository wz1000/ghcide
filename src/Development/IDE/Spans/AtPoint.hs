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
  , showName
  , defRowToSymbolInfo
  ) where

import           Development.IDE.GHC.Error
import Development.IDE.GHC.Orphans()
import Development.IDE.Types.Location
import           Language.Haskell.LSP.Types

-- DAML compiler and infrastructure
import Development.IDE.GHC.Compat
import Development.IDE.Types.Options
import Development.IDE.Spans.Common

-- GHC API imports
import DynFlags
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

import System.IO.Unsafe


import IfaceType
import Data.Either
import Data.List.Extra (dropEnd)

import HieDb (HieDb, search,RefRow(..), findDef, DefRow(..), Res, (:.)(..),ModuleInfo(..), dynFlagsForPrinting)

type LookupModule m = ModuleName -> UnitId -> Bool -> MaybeT m Uri

rowToLoc :: Monad m => LookupModule m -> Res RefRow -> m (Maybe Location)
rowToLoc lookupModule (row:.info) = do
  mfile <- case modInfoSrcFile info of
    Just f -> pure $ Just $ toUri f
    Nothing -> runMaybeT $ lookupModule (modInfoName info) (modInfoUnit info) (modInfoIsBoot info)
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
        pure $ maybe [] (map $ srcSpanToLocation . RealSrcSpan . fst) $ M.lookup (Right name) rf
      Just mod -> do
         rows <- liftIO $ search hiedb (nameOccName name) (Just $ moduleName mod) (Just $ moduleUnitId mod)
         lift $ mapMaybeM (rowToLoc lookupModule) rows
  pure $ concat locs

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
  -> Position
  -> MaybeT m [Location]
gotoTypeDefinition hiedb lookupModule ideOpts srcSpans pos
  = lift $ typeLocationsAtPoint hiedb lookupModule ideOpts pos srcSpans

-- | Locate the definition of the name at a given position.
gotoDefinition
  :: MonadIO m
  => HieDb
  -> LookupModule m
  -> IdeOptions
  -> HieFile
  -> Position
  -> MaybeT m [Location]
gotoDefinition hiedb lookupModule ideOpts srcSpans pos =
  lift $ locationsAtPoint hiedb lookupModule ideOpts pos srcSpans

-- | Synopsis for the name at a given position.
atPoint
  :: IdeOptions
  -> HieFile
  -> DocMap
  -> Position
  -> Maybe (Maybe Range, [T.Text])
atPoint IdeOptions{} hf dm pos = listToMaybe $ pointCommand hf pos hoverInfo
  where
    -- Hover info for values/data
    hoverInfo ast =
      (Just range, prettyNames ++ pTypes)
      where
        pTypes
          | length names == 1 = dropEnd 1 $ map wrapHaskell prettyTypes
          | otherwise = map wrapHaskell prettyTypes

        range = realSrcSpanToRange $ nodeSpan ast

        wrapHaskell x = "\n```haskell\n"<>x<>"\n```\n"
        info = nodeInfo ast
        names = M.assocs $ nodeIdentifiers info
        types = nodeType info

        prettyNames :: [T.Text]
        prettyNames = map prettyName names
        prettyName (Right n, dets) = T.unlines $
          wrapHaskell (showName n <> maybe "" (" :: " <> ) (prettyType <$> identType dets))
          : definedAt n
          : concat (maybeToList (spanDocToMarkdown <$> M.lookup n dm))
        prettyName (Left m,_) = showName m

        prettyTypes = map (("_ :: "<>) . prettyType) types
        prettyType t = showName $ hieTypeToIface $ recoverFullType t arr

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
  -> m [Location]
typeLocationsAtPoint hiedb lookupModule _ideOptions pos ast =
  let ts = concat $ pointCommand ast pos (nodeType . nodeInfo)
      arr = hie_types ast
      its = map (arr A.!) ts
      ns = flip mapMaybe its $ \case
        HTyConApp tc _ -> Just $ ifaceTyConName tc
        HTyVarTy n -> Just n
        _ -> Nothing
    in concatMapM (fmap (maybe [] id) . nameToLocation hiedb lookupModule) ns

locationsAtPoint
  :: forall m
   . MonadIO m
  => HieDb
  -> LookupModule m
  -> IdeOptions
  -> Position
  -> HieFile
  -> m [Location]
locationsAtPoint hiedb lookupModule _ideOptions pos ast =
  let ns = concat $ pointCommand ast pos (rights . M.keys . nodeIdentifiers . nodeInfo)
    in concatMapM (fmap (maybe [] id) . nameToLocation hiedb lookupModule) ns

-- | Given a 'Name' attempt to find the location where it is defined.
nameToLocation :: MonadIO m => HieDb -> LookupModule m -> Name -> m (Maybe [Location])
nameToLocation hiedb lookupModule name = runMaybeT $
  case nameSrcSpan name of
    sp@(RealSrcSpan _) -> MaybeT $ pure $ fmap pure $ srcSpanToLocationMaybe sp
    sp@(UnhelpfulSpan _) -> do
      guard (sp /= wiredInSrcSpan)
      -- This case usually arises when the definition is in an external package.
      -- In this case the interface files contain garbage source spans
      -- so we instead read the .hie files to get useful source spans.
      mod <- MaybeT $ return $ nameModule_maybe name
      erow <- liftIO $ findDef hiedb (nameOccName name) (Just $ moduleName mod) (Just $ moduleUnitId mod)
      case erow of
        [] -> MaybeT $ pure Nothing
        xs -> lift $ mapMaybeM (runMaybeT . defRowToLocation lookupModule) xs

defRowToLocation :: Monad m => LookupModule m -> Res DefRow -> MaybeT m Location
defRowToLocation lookupModule (row:.info) = do
  let start = Position (defSLine row - 1) (defSCol row - 1)
      end   = Position (defELine row - 1) (defECol row - 1)
      range = Range start end
  file <- case modInfoSrcFile info of
    Just src -> pure $ toUri src
    Nothing -> lookupModule (modInfoName info) (modInfoUnit info) (modInfoIsBoot info)
  pure $ Location file range

toUri :: FilePath -> Uri
toUri = fromNormalizedUri . filePathToUri' . toNormalizedFilePath'

defRowToSymbolInfo :: Res DefRow -> SymbolInformation
defRowToSymbolInfo (DefRow{..}:._)
  = SymbolInformation (showName defNameOcc) kind Nothing loc Nothing
  where
    kind
      | isVarOcc defNameOcc = SkVariable
      | isDataOcc defNameOcc = SkConstructor
      | isTcOcc defNameOcc = SkStruct
      | otherwise = SkUnknown 1
    loc   = Location file range
    file  = fromNormalizedUri . filePathToUri' . toNormalizedFilePath' $ defFile
    range = Range start end
    start = Position (defSLine - 1) (defSCol - 1)
    end   = Position (defELine - 1) (defECol - 1)

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

showName :: Outputable a => a -> T.Text
showName = showSD . ppr

showSD :: SDoc -> T.Text
showSD = T.pack . prettyprint
  where
    prettyprint x = renderWithStyle printDynFlags x style
    style = mkUserStyle printDynFlags neverQualify AllTheWay

printDynFlags :: DynFlags
printDynFlags = unsafePerformIO dynFlagsForPrinting
