module Macro.Index where

import           Types

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

