module Probability.Independence.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro

ind :: Note -> Note -> Note
ind = binop $ comm0 "bot"

cind :: Note -> Note -> Note -> Note
cind a b c = pars (ind a b) <> mid <> c

