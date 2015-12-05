module Macro.Todo where

import           Types

import           Control.Monad (unless)

todo' :: LaTeXC l => l -> l
todo' = liftL $ \l -> TeXComm "todo" [MOptArg ["color=red", "inline", raw "size=\\small"], FixArg l ]

todo :: Note -> Note
todo n = do
    o <- asks conf_omitTodos
    unless o $ todo' n

toprove :: Note
toprove = todo $ "There is a proof missing here."

toprove_ :: Note -> Note
toprove_ n = todo $ do
  n
  newline
  "There is a proof missing here."

noproof :: Note
noproof = todo "There either is a proof missing here or a confirmation that no proof is required at all."

noproof_ :: Note
noproof_ = footnotesize "No proof."

exneeded :: Note
exneeded = todo "There is an example missing here."

cexneeded :: Note
cexneeded = todo "There is an counter example missing here."


refneeded :: Note -> Note
refneeded n = todo $ do
  "There is a reference to "
  raw "``" <> n <> raw "''"
  " missing here. "

citneeded :: Note
citneeded = todo "Citation needed"

totheorem :: Note -> Note
totheorem th = todo $ "TODO, theorem: " <> th
