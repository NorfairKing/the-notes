module Cryptography.ComputationalProblems.Games.DistinctionProblems.Macro where

import           Types

import           Macro.MetaMacro

import           Functions.Application.Macro

-- * Distinction problems

objs_ :: Note
objs_ = mathcal "O"

dprob :: Note -> Note -> Note
dprob s1 s2 = autoBrackets langle rangle $ s1 <> comm0 "mid" <> s2

guess_ :: Note
guess_ = kappa

guess :: Note -> Note -> Note
guess = fn2 guess_

-- ** Distinguisher's advantage
-- | A given Distinguisher's advantage
dadv_ :: Note
dadv_ = comm0 "Delta"

dadv :: Note -> Note -> Note -> Note
dadv d = fn2 $ dadv_ ^: d

-- | Distinguishers' advantage
dadvs :: Note -> Note -> Note
dadvs = fn2 $ dadv_

