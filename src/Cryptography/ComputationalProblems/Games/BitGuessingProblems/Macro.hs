module Cryptography.ComputationalProblems.Games.BitGuessingProblems.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro

import           Functions.Application.Macro

-- * Bit guessing problems

bgprob :: Note -> Note -> Note
bgprob s z = sqbrac $ s <> "; " <> z

-- Guesser's advantage in given bit guessing problem
gadvf :: Note -> Note
gadvf = ("A" !:)

gadv :: Note -> Note -> Note
gadv p = fn $ gadvf p


-- * Discrete games

-- ** Stop symbol for discrete distinguishers
stopsym_ :: Note
stopsym_ = comm0 "dashv"

stopsym :: Note -> Note
stopsym = (stopsym_ !:)
