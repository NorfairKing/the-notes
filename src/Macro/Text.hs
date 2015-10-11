module Macro.Text where

import           Types

import           Prelude (sequence_)

-- Shorter than sequence_
-- To model a sentence.
s :: [Note] -> Note
s ns = do
  sequence_ ns
  " "

quoted :: Note -> Note
quoted n = "`" <> n <> "'"

dquoted :: Note -> Note
dquoted n = "``" <> n <> "''"

commaSeparated :: [Note] -> Note
commaSeparated [] = ""
commaSeparated [n] = n
commaSeparated (n:ns) = n <> ", " <> commaSeparated ns

cs :: [Note] -> Note
cs = commaSeparated
