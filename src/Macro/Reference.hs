module Macro.Reference where

import           Reference
import           Types

import qualified Text.LaTeX.Base.Commands as T (pageref, ref)


wordOf :: RefKind -> Note
wordOf Definition     = "Definition"
wordOf Theorem        = "theorem"
wordOf Property       = "property"
wordOf Proposition    = "proposition"

refKind :: Label -> RefKind
refKind (Label kind _) = kind

wordFor :: Label -> Note
wordFor = wordOf . refKind

labelOf :: Label -> Note
labelOf (Label _ n) = n

labelFor :: Label -> Note
labelFor l = wordFor l <> ":" <> labelOf l

ref :: Label -> Note
ref l = footnote $ "See " <> wordFor l <> " " <> T.ref (labelFor l) <> " on page " <> T.pageref (labelFor l) <> "."

lab :: Label -> Note
lab l = label $ labelFor l

delab :: Note -> Label
delab = Label Definition

thmlab :: Note -> Label
thmlab = Label Theorem

proplab :: Note -> Label
proplab = Label Property

prolab :: Note -> Label
prolab = Label Proposition


cite :: Reference -> Note
cite = comm1 "cite" . refName

nocite :: Reference -> Note
nocite = comm1 "nocite" . refName
