module Macro.Index where

import           Types

printindex :: Note
printindex = do
    packageDep_ "makeidx"
    comm0 "printindex"

makeindex :: Note
makeindex = do
    packageDep_ "makeidx"
    commS "makeindex"

index :: Note -> Note
index n = do
    packageDep_ "makeidx"
    comm1 "index" n

ix :: Note -> Note
ix text = ix_ text text

ix_ :: Note -> Note -> Note
ix_ text ind = do
    index ind
    text

emphTerm :: Note -> Note
emphTerm = textbf

defineTerm :: Note -> Note
defineTerm text = defineTerm_ text text

defineTerm_ :: Note -> Note -> Note
defineTerm_ text ind = do
    index ind
    emphTerm text

