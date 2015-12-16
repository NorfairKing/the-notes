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
index = comm1 "index"

ix :: Note -> Note
ix text = do
    index text
    text

term :: Note -> Note
term text = do
    index text
    textbf text

