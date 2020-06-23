{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
#include "ghc-api-version.h"

module Development.IDE.Spans.Common (
  showGhc
, showName
, safeTyThingId
#ifndef GHC_LIB
, safeTyThingType
#endif
, SpanDoc(..)
, SpanDocUris(..)
, emptySpanDoc
, spanDocToMarkdown
, spanDocToMarkdownForTest
, DocMap
) where

import Data.Maybe
import qualified Data.Text as T
import Data.List.Extra
import Data.Map (Map)

import GHC
import Outputable hiding ((<>))
import DynFlags
import ConLike
import DataCon
#ifndef GHC_LIB
import Var
#endif

import qualified Documentation.Haddock.Parser as H
import qualified Documentation.Haddock.Types as H

import HieDb (dynFlagsForPrinting)
import System.IO.Unsafe

type DocMap = Map Name SpanDoc

showGhc :: Outputable a => a -> String
showGhc = showPpr printDynFlags

showName :: Outputable a => a -> T.Text
showName = showSD . ppr

showSD :: SDoc -> T.Text
showSD = T.pack . prettyprint
  where
    prettyprint x = renderWithStyle printDynFlags x style
    style = mkUserStyle printDynFlags neverQualify AllTheWay

printDynFlags :: DynFlags
printDynFlags = unsafePerformIO dynFlagsForPrinting

#ifndef GHC_LIB
-- From haskell-ide-engine/src/Haskell/Ide/Engine/Support/HieExtras.hs
safeTyThingType :: TyThing -> Maybe Type
safeTyThingType thing
  | Just i <- safeTyThingId thing = Just (varType i)
safeTyThingType (ATyCon tycon)    = Just (tyConKind tycon)
safeTyThingType _                 = Nothing
#endif

safeTyThingId :: TyThing -> Maybe Id
safeTyThingId (AnId i)                    = Just i
safeTyThingId (AConLike (RealDataCon dc)) = Just $ dataConWrapId dc
safeTyThingId _                           = Nothing

-- Possible documentation for an element in the code
data SpanDoc
  = SpanDocString HsDocString SpanDocUris
  | SpanDocText   [T.Text] SpanDocUris
  deriving Show

data SpanDocUris =
  SpanDocUris
  { spanDocUriDoc :: Maybe T.Text -- ^ The haddock html page
  , spanDocUriSrc :: Maybe T.Text -- ^ The hyperlinked source html page
  } deriving Show

emptySpanDoc :: SpanDoc
emptySpanDoc = SpanDocText [] (SpanDocUris Nothing Nothing)

spanDocToMarkdown :: SpanDoc -> [T.Text]
#if MIN_GHC_API_VERSION(8,6,0)
spanDocToMarkdown (SpanDocString docs uris)
  = [T.pack $ haddockToMarkdown $ H.toRegular $ H._doc $ H.parseParas Nothing $ unpackHDS docs]
    <> ["\n"] <> spanDocUrisToMarkdown uris
  -- Append the extra newlines since this is markdown --- to get a visible newline,
  -- you need to have two newlines
#else
spanDocToMarkdown (SpanDocString _ uris)
  = spanDocUrisToMarkdown uris
#endif
spanDocToMarkdown (SpanDocText txt uris) = txt <> ["\n"] <> spanDocUrisToMarkdown uris

spanDocUrisToMarkdown :: SpanDocUris -> [T.Text]
spanDocUrisToMarkdown (SpanDocUris mdoc msrc) = catMaybes
  [ linkify "Documentation" <$> mdoc
  , linkify "Source" <$> msrc
  ]
  where linkify title uri = "[" <> title <> "](" <> uri <> ")"

spanDocToMarkdownForTest :: String -> String
spanDocToMarkdownForTest
  = haddockToMarkdown . H.toRegular . H._doc . H.parseParas Nothing

-- Simple (and a bit hacky) conversion from Haddock markup to Markdown
haddockToMarkdown
  :: H.DocH String String -> String

haddockToMarkdown H.DocEmpty
  = ""
haddockToMarkdown (H.DocAppend d1 d2)
  = haddockToMarkdown d1 ++ " " ++ haddockToMarkdown d2
haddockToMarkdown (H.DocString s)
  = s
haddockToMarkdown (H.DocParagraph p)
  = "\n\n" ++ haddockToMarkdown p
haddockToMarkdown (H.DocIdentifier i)
  = "`" ++ i ++ "`"
haddockToMarkdown (H.DocIdentifierUnchecked i)
  = "`" ++ i ++ "`"
haddockToMarkdown (H.DocModule i)
  = "`" ++ i ++ "`"
haddockToMarkdown (H.DocWarning w)
  = haddockToMarkdown w
haddockToMarkdown (H.DocEmphasis d)
  = "*" ++ haddockToMarkdown d ++ "*"
haddockToMarkdown (H.DocBold d)
  = "**" ++ haddockToMarkdown d ++ "**"
haddockToMarkdown (H.DocMonospaced d)
  = "`" ++ escapeBackticks (haddockToMarkdown d) ++ "`"
  where
    escapeBackticks "" = ""
    escapeBackticks ('`':ss) = '\\':'`':escapeBackticks ss
    escapeBackticks (s  :ss) = s:escapeBackticks ss
haddockToMarkdown (H.DocCodeBlock d)
  = "\n```haskell\n" ++ haddockToMarkdown d ++ "\n```\n"
haddockToMarkdown (H.DocExamples es)
  = "\n```haskell\n" ++ unlines (map exampleToMarkdown es) ++ "\n```\n"
  where
    exampleToMarkdown (H.Example expr result)
      = ">>> " ++ expr ++ "\n" ++ unlines result
haddockToMarkdown (H.DocHyperlink (H.Hyperlink url Nothing))
  = "<" ++ url ++ ">"
haddockToMarkdown (H.DocHyperlink (H.Hyperlink url (Just label)))
  = "[" ++ haddockToMarkdown label ++ "](" ++ url ++ ")"
haddockToMarkdown (H.DocPic (H.Picture url Nothing))
  = "![](" ++ url ++ ")"
haddockToMarkdown (H.DocPic (H.Picture url (Just label)))
  = "![" ++ label ++ "](" ++ url ++ ")"
haddockToMarkdown (H.DocAName aname)
  = "[" ++ aname ++ "]:"
haddockToMarkdown (H.DocHeader (H.Header level title))
  = replicate level '#' ++ " " ++ haddockToMarkdown title

haddockToMarkdown (H.DocUnorderedList things)
  = '\n' : (unlines $ map (("+ " ++) . trimStart . splitForList . haddockToMarkdown) things)
haddockToMarkdown (H.DocOrderedList things)
  = '\n' : (unlines $ map (("1. " ++) . trimStart . splitForList . haddockToMarkdown) things)
haddockToMarkdown (H.DocDefList things)
  = '\n' : (unlines $ map (\(term, defn) -> "+ **" ++ haddockToMarkdown term ++ "**: " ++ haddockToMarkdown defn) things)

-- we cannot render math by default
haddockToMarkdown (H.DocMathInline _)
  = "*cannot render inline math formula*"
haddockToMarkdown (H.DocMathDisplay _)
  = "\n\n*cannot render display math formula*\n\n"

-- TODO: render tables
haddockToMarkdown (H.DocTable _t)
  = "\n\n*tables are not yet supported*\n\n"

-- things I don't really know how to handle
haddockToMarkdown (H.DocProperty _)
  = ""  -- don't really know what to do

splitForList :: String -> String
splitForList s
  = case lines s of
      [] -> ""
      (first:rest) -> unlines $ first : map (("  " ++) . trimStart) rest
