module Macro.Reference where

import           Types

import           Control.Monad        (mapM_, when)
import           Control.Monad.Reader (asks)

import qualified Text.LaTeX.LambdaTeX as T (label, pageref, ref)

wordOf :: RefKind -> Text
wordOf Definition     = "definition"
wordOf Theorem        = "theorem"
wordOf Property       = "property"
wordOf Proposition    = "proposition"
wordOf Example        = "example"
wordOf Figure         = "figure"
wordOf Note           = "note"

refKind :: Label -> RefKind
refKind (MkLabel kind _) = kind

wordFor :: Label -> Text
wordFor = wordOf . refKind

labelOf :: Label -> Text
labelOf (MkLabel _ n) = n

labelFor :: Label -> Text
labelFor l = wordFor l <> ":" <> labelOf l

ref :: Label -> Note
ref l = footnote $ do
    debug <- asks conf_visualDebug
    let ll = labelFor l
    "See "
    fromLaTeX $ TeXRaw $ wordFor l
    " "
    T.ref ll
    " on page "
    T.pageref ll
    "."
    " "
    when debug $ labelBox l

refs :: [Label] -> Note
refs rs = (<> newline) $ mapM_ ref rs

labelBox :: Label -> Note
labelBox l = colorbox (ModColor $ RGB 0.5 0.5 0.5) $ textcolor (ModColor $ RGB 0 1 0) ll
  where ll = fromLaTeX $ TeXRaw $ labelFor l

lab :: Label -> Note
lab l = do
    debug <- asks conf_visualDebug
    let ll = labelFor l
    when debug $ labelBox l <> lnbk
    T.label ll
