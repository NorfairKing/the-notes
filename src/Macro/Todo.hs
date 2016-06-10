module Macro.Todo where

import           Types

import           Macro.Text
import           Macro.Theorem

import           Control.Monad        (when)
import           Control.Monad.Reader (asks)

listoftodos :: Note
listoftodos = do
    o <- asks conf_todos
    when o $ do
        packageDep_ "todonotes"
        comm0 "listoftodos"


coloredTodo' :: LaTeXC l => l -> l -> l
coloredTodo' = liftL2 (\color l -> TeXComm "todo" [MOptArg ["color=" <> color, "inline", raw "size=\\small"], FixArg l ])

coloredTodo :: Note -> Note -> Note
coloredTodo color n = do
    o <- asks conf_todos
    when o $ do
        packageDep_ "todonotes"
        coloredTodo' color n

todo :: Note -> Note
todo = coloredTodo "red"

clarify :: Note -> Note
clarify n = coloredTodo "yellow" $ "Clarify: " <> n

toprove :: Note
toprove = coloredTodo "orange" $ "There is a proof missing here."

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

why :: Note
why = clarify $ "Why? More of an explanation is missing here."

why_ :: Note -> Note
why_ n = clarify $ "Why " <> n <> "?" <> " " <> "More of an explanation is missing here."


-- | Placeholder for future references
placeholder :: Note -> Note
placeholder n = thm $ do
    s ["This is a placeholder for future references"]
    n
