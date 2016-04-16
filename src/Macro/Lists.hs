module Macro.Lists where

import           Types

import           Macro.Math
import           Macro.Text

-- | List of arbitrary content
listof :: Note -> Note
listof = autoSquareBrackets

-- | List of elements
listofs :: [Note] -> Note
listofs = autoSquareBrackets . cs

-- | Empty list
nil :: Note
nil = "[]"

-- | Singleton list
sing :: Note -> Note
sing = listof

-- | Building a list
cns :: Note -> Note -> Note
cns e es = e <> ":" <> es

listlst :: Note -> Note -> Note
listlst a z = listofs [a, dotsc, z]

listlist :: Note -> Note -> Note -> Note
listlist a b z = listofs [a, b, dotsc, z]
