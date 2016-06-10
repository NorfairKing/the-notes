module Cryptography.ComputationalProblems.Games.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro
import           Macro.Tuple

import           Functions.Application.Macro
import           Logic.PropositionalLogic.Macro

import           Cryptography.ComputationalProblems.Abstract.Macro

-- * Games

-- ** Winning condition
wins_ :: Note
wins_ = omega

wins :: Note -> Note -> Note
wins = fn2 wins_

-- ** Deterministic games
gme_ :: Note
gme_ = "g"

plr_ :: Note
plr_ = "w"

-- ** Probabillistic games
gmev_ :: Note
gmev_ = "G"

plrv_ :: Note
plrv_ = "W"

-- * Multigames

winsub_ :: Note -> Note
winsub_ = (wins_ !:)

winsub :: Note -> Note -> Note -> Note
winsub i = fn2 $ winsub_ i

orgame :: Note -> Note
orgame = (^: ("" ∨ ""))

andgame :: Note -> Note
andgame = (^: ("" ∧ ""))

-- * Search problems

-- | Search problem
sprob :: Note -- ^ Instance space
      -> Note -- ^ Witness space
      -> Note -- ^ Predicate
      -> Note -- ^ Probability distribution
      -> Note
sprob = quadruple

-- | Instance space
isp_ :: Note
isp_ = mathcal "X"

-- | Witness space
wsp_ :: Note
wsp_ = mathcal "W"

-- | Search space predicate
spred_ :: Note
spred_ = "Q"

-- | Search problem probability distribution
sppd_ :: Note
sppd_ = probl_ !: isp_

-- | Concrete search problem
sprob_ :: Note
sprob_ = sprob isp_ wsp_ spred_ sppd_

-- | solution predicate
sol :: Note -> Note -> Note
sol = fn2 spred_


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

-- * Bit guessing problems

bgprob :: Note -> Note -> Note
bgprob s z = sqbrac $ s <> "; " <> z

-- Guesser's advantage in given bit guessing problem
gadvf :: Note -> Note
gadvf = ("A" !:)

gadv :: Note -> Note -> Note
gadv p = fn $ gadvf p
