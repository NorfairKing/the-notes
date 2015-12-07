module Relations.Composite.Macro where

import           Macro.MetaMacro (binop)

import           Types

-- * Relation Composition
comp :: Note -> Note -> Note
comp = binop $ comm0 "circ"

-- |
-- > C-k 0M
(●) :: Note -> Note -> Note
(●) = comp
