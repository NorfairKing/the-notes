module Cryptography.ComputationalProblems.Games.DiscreteGames.Macro where

import           Types

import           Macro.MetaMacro


-- * Discrete games

-- ** Stop symbol for discrete distinguishers
stopsym_ :: Note
stopsym_ = comm0 "dashv"

stopsym :: Note -> Note
stopsym = (stopsym_ !:)
