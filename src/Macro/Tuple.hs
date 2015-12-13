module Macro.Tuple where

import           Types

import           Macro.Math
import           Macro.Text

-- * Tuples

-- | 2-tuple
tuple :: Note -> Note -> Note
tuple a b = pars $ commaSeparated [a, b]

-- | 3-tuple
triple :: Note -> Note -> Note -> Note
triple a b c = pars $ commaSeparated [a, b, c]

-- | 4-tuple
quadruple :: Note -> Note -> Note -> Note -> Note
quadruple a b c d = pars $ commaSeparated [a, b, c, d]

-- | 5-tuple
quintuple :: Note -> Note -> Note -> Note -> Note -> Note
quintuple a b c d e = pars $ commaSeparated [a, b, c, d, e]

-- | Tuple list
tuplelst :: Note -> Note -> Note
tuplelst x1 xn = pars $ lst x1 xn

-- | Tuple list
tuplelist :: Note -> Note -> Note -> Note
tuplelist x1 x2 xn = pars $ list x1 x2 xn


