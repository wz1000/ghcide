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

import Control.Monad.Extra
import Control.Monad.Trans.Maybe
import Control.Monad.IO.Class
import           Data.Maybe
import           Data.List
import qualified Data.Text as T
import qualified Data.Map as M
import qualified Data.Array as A


import IfaceType
import Data.Either

import HieDb (HieDb, search,RefRow(..))

referencesAtPoint
  :: MonadIO m
  => HieDb
  -> HieFile
  -> RefMap
  -> Position
  -> MaybeT m [Location]
referencesAtPoint hiedb hf rf pos = do
  let names = concat $ pointCommand hf pos (rights . M.keys . nodeIdentifiers . nodeInfo)
      rowToLoc row = Location file range
        where
          file = fromNormalizedUri $ filePathToUri' $ toNormalizedFilePath' $ refFile row
          range = Range start end
          start = Position (refSLine row - 1) (refSCol row -1)
          end = Position (refELine row - 1) (refECol row -1)
  locs <- forM names $ \name ->
    case nameModule_maybe name of
      Nothing ->
        pure $ maybe [] (map $ srcSpanToLocation . RealSrcSpan . fst) $ M.lookup (Right name) rf
      Just mod -> do
         rows <- liftIO $ search hiedb (nameOccName name) (Just $ moduleName mod) (Just $ moduleUnitId mod)
         pure $ map rowToLoc rows
  pure $ concat locs

documentHighlight
  :: Monad m
  => HieFile
  -> RefMap
  -> Position
  -> MaybeT m [DocumentHighlight]
documentHighlight hf rf pos = MaybeT $ pure (Just highlights)
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
  => (Module -> MaybeT m (HieFile, FilePath))
  -> IdeOptions
  -> HieFile
  -> Position
  -> MaybeT m Location
gotoTypeDefinition getHieFile ideOpts srcSpans pos
  = MaybeT (listToMaybe <$> typeLocationsAtPoint getHieFile ideOpts pos srcSpans)

-- | Locate the definition of the name at a given position.
gotoDefinition
  :: MonadIO m
  => (Module -> MaybeT m (HieFile, FilePath))
  -> IdeOptions
  -> HieFile
  -> Position
  -> MaybeT m Location
gotoDefinition getHieFile ideOpts srcSpans pos =
  MaybeT (listToMaybe <$> locationsAtPoint getHieFile ideOpts pos srcSpans)

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
      (Just range, prettyNames ++ map wrapHaskell prettyTypes)
      where
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
  => (Module -> MaybeT m (HieFile, FilePath))
  -> IdeOptions
  -> Position
  -> HieFile
  -> m [Location]
typeLocationsAtPoint getHieFile _ideOptions pos ast =
  let ts = concat $ pointCommand ast pos (nodeType . nodeInfo)
      arr = hie_types ast
      its = map (arr A.!) ts
      ns = flip mapMaybe its $ \case
        HTyConApp tc _ -> Just $ ifaceTyConName tc
        HTyVarTy n -> Just n
        _ -> Nothing
    in mapMaybeM (nameToLocation getHieFile) ns

locationsAtPoint
  :: forall m
   . MonadIO m
  => (Module -> MaybeT m (HieFile, FilePath))
  -> IdeOptions
  -> Position
  -> HieFile
  -> m [Location]
locationsAtPoint getHieFile _ideOptions pos ast =
  let ns = concat $ pointCommand ast pos (rights . M.keys . nodeIdentifiers . nodeInfo)
    in mapMaybeM (nameToLocation getHieFile) ns

-- | Given a 'Name' attempt to find the location where it is defined.
nameToLocation :: Monad f => (Module -> MaybeT f (HieFile, String)) -> Name -> f (Maybe Location)
nameToLocation getHieFile name = fmap (srcSpanToLocationMaybe =<<) $
              case nameSrcSpan name of
                sp@(RealSrcSpan _) -> pure $ Just sp
                sp@(UnhelpfulSpan _) -> runMaybeT $ do
                  guard (sp /= wiredInSrcSpan)
                  -- This case usually arises when the definition is in an external package.
                  -- In this case the interface files contain garbage source spans
                  -- so we instead read the .hie files to get useful source spans.
                  mod <- MaybeT $ return $ nameModule_maybe name
                  (hieFile, srcPath) <- getHieFile mod
                  avail <- MaybeT $ pure $ find (eqName name . snd) $ hieExportNames hieFile
                  -- The location will point to the source file used during compilation.
                  -- This file might no longer exists and even if it does the path will be relative
                  -- to the compilation directory which we don’t know.
                  let span = setFileName srcPath $ fst avail
                  pure span
  where
    -- We ignore uniques and source spans and only compare the name and the module.
    eqName :: Name -> Name -> Bool
    eqName n n' = nameOccName n == nameOccName n' && nameModule_maybe n == nameModule_maybe n'
    setFileName f (RealSrcSpan span) = RealSrcSpan (span { srcSpanFile = mkFastString f })
    setFileName _ span@(UnhelpfulSpan _) = span

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
showName = T.pack . prettyprint
  where
    prettyprint x = renderWithStyle unsafeGlobalDynFlags (ppr x) style
    style = mkUserStyle unsafeGlobalDynFlags neverQualify AllTheWay

