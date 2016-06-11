module Cryptography.ComputationalProblems.Games.DiscreteGames.Macro where

import           Types

import           Functions.Application.Macro
import           Macro.Arrows
import           Macro.Math
import           Macro.MetaMacro


-- * Discrete games

-- ** Stop symbol for discrete distinguishers
stopsym_ :: Note
stopsym_ = comm0 "dashv"

stopsym :: Note -> Note
stopsym = (stopsym_ !:)

-- * Reductions for discrete games

-- ** Reduction by transformer

-- | Reduction by given transformer
tred_ :: Note -> Note
tred_ = overset rightarrow

tred :: Note -> Note -> Note
tred = fn . tred_

-- ** Reduction by multiple invocations
mred_ :: Note -> Note
mred_ = (pars cdot_ ^)

mred :: Note -> Note -> Note
mred = (^)

