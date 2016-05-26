{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Macro.Text where

import           Types

import           Data.List (intersperse)
import           Prelude   (error, length, otherwise, sequence_, (++), (<))
import           TH

-- Polyvariadic version of 's'.
p :: NoteArgs args => args
p = noteArgs []

class NoteArgs t where
    noteArgs :: [Note] -> t

instance NoteArgs Note where
    -- noteArgs :: [Note] -> Note
    noteArgs = s

-- The equality constraint Note ~ note is what makes it all work.
-- Otherwise the type checker wouldn't have been able to figure out that
-- String literals should be interpreted as Note's.
instance (Note ~ note, NoteArgs r) => NoteArgs (note -> r) where
    -- noteArgs :: [Note] -> ([Note] -> r)
    noteArgs ns n = noteArgs $ ns ++ [n]

-- FIXME find a way to add an instance for NoteArgs ([note] -> r), then the old 's' will work.

-- Shorter than sequence_
-- To model a sentence.
s :: [Note] -> Note
s ns = do
    sequence_ $ intersperse " " ns
    ". "

makeStrs
    [ "holds"
    , "equals"
    , "define"
    , "respectively"
    , "because"
    , "but"
    , "at"
    , "to"
    , "from"
    , "be"
    , "with"
    , "for"
    , "on"
    , "by"
    , "over"
    , "are"
    , "is"
    , "or"
    , "and"
    , "The"
    , "a"
    ]

makeAbbrs
    [ ("anda", "and a")
    , ("andan", "and an")
    , ("wrt", "with respect to")
    , ("beA", "be a")
    , ("beAn", "be an")

    , ("kul", "KU Leuven")
    , ("eth", "ETH")
    ]

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

commaSeparatedWord :: Note -> [Note] -> Note
commaSeparatedWord word ns
    | length ns < 2 = commaSeparated ns
    | otherwise = go ns
  where
    go [] = error "impossible as per three lines above"
    go [n] = word <> " " <> n
    go (n:ns) = n <> ", " <> go ns

commaSeparatedAnd :: [Note] -> Note
commaSeparatedAnd = commaSeparatedWord and

commaSeparatedOr :: [Note] -> Note
commaSeparatedOr = commaSeparatedWord or

csa :: [Note] -> Note
csa = commaSeparatedAnd

cso :: [Note] -> Note
cso = commaSeparatedOr
