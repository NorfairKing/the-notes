module Macro.Text where

import           Types

-- Shorter than sequence_
-- To model a sentence.
s :: [Note] -> Note
s ns = do
  sequence_ ns
  " "

quoted :: Note -> Note
quoted n = "`" <> n <> "'"
