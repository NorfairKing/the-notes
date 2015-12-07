module Macro.Reference where

import           Control.Monad            (when)

import           Reference
import           Types

import qualified Text.LaTeX.Base.Commands as T (pageref, ref)


wordOf :: RefKind -> Note
wordOf Definition     = "definition"
wordOf Theorem        = "theorem"
wordOf Property       = "property"
wordOf Proposition    = "proposition"
wordOf Example        = "example"

refKind :: Label -> RefKind
refKind (Label kind _) = kind

wordFor :: Label -> Note
wordFor = wordOf . refKind

labelOf :: Label -> Note
labelOf (Label _ n) = n

labelFor :: Label -> Note
labelFor l = wordFor l <> ":" <> labelOf l

ref :: Label -> Note
ref l = footnote $ do
    debug <- asks conf_visualDebug
    let ll = labelFor l
    "See "
    wordFor l
    " "
    T.ref ll
    " on page "
    T.pageref ll
    "."
    " "
    when debug $ labelBox l

labelBox :: Label -> Note
labelBox l = colorbox (ModColor $ RGB 0.5 0.5 0.5) $ textcolor (ModColor $ RGB 0 1 0) ll
  where ll = labelFor l

lab :: Label -> Note
lab l = do
    debug <- asks conf_visualDebug
    let ll = labelFor l
    when debug $ labelBox l <> lnbk
    label ll

delab :: Note -> Label
delab = Label Definition

thmlab :: Note -> Label
thmlab = Label Theorem

proplab :: Note -> Label
proplab = Label Property

prolab :: Note -> Label
prolab = Label Proposition


cite :: Reference -> Note
cite ref = do
  comm1 "cite" $ refName ref
  addReference ref

nocite :: Reference -> Note
nocite ref = do
  comm1 "nocite" $ refName ref
  addReference ref
