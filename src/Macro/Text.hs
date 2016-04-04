module Macro.Text where

import           Types

import           Data.List (intersperse)
import           Prelude   (error, length, otherwise, sequence_, (<))

-- Shorter than sequence_
-- To model a sentence.
s :: [Note] -> Note
s ns = do
    sequence_ $ intersperse " " ns
    ". "

quoted :: Note -> Note
quoted n = "`" <> n <> "'"

dquoted :: Note -> Note
dquoted n = raw "``" <> n <> raw "''"

separated :: Note -> [Note] -> Note
separated _ [] = ""
separated _ [n] = n
separated delim (n:ns) = n <> delim <> separated delim ns

commaSeparated :: [Note] -> Note
commaSeparated = separated ", "

cs :: [Note] -> Note
cs = commaSeparated

commaSeparatedAnd :: [Note] -> Note
commaSeparatedAnd ns
    | length ns < 2 = commaSeparated ns
    | otherwise = go ns
  where
    go [] = error "impossible as per three lines above"
    go [n] = and <> " " <> n
    go (n:ns) = n <> ", " <> go ns

csa :: [Note] -> Note
csa = commaSeparatedAnd

and :: Note
and = "and"

anda :: Note
anda = "and a"

andan :: Note
andan = "and an"

or :: Note
or = "or"

is :: Note
is = "is"

the :: Note
the = "The"

by :: Note
by = "by"

on :: Note
on = "on"

over :: Note
over = "over"

wrt :: Note
wrt = "with respect to"

for :: Note
for = "for"

with :: Note
with = "with"

be :: Note
be = "be"

beA :: Note
beA = "be a"

beAn :: Note
beAn = "be an"

from :: Note
from = "from"

to :: Note
to = "to"

at :: Note
at = "at"

kul :: Note
kul = "KU Leuven"

eth :: Note
eth = "ETH"

