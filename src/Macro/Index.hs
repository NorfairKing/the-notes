module Macro.Index where

import           Types

index :: Note -> Note
index = comm1 "index"

ix :: Note -> Note
ix text = do
    index text
    text
    " "  -- For easier use.
         -- Leaving it out is trouble,
         -- putting it in makes no difference if you ignore it.

term :: Note -> Note
term text = do
    index text
    textbf text

