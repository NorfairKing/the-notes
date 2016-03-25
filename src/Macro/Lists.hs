module Macro.Lists where

import           Types

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
