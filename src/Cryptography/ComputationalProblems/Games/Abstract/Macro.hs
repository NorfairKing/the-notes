module Cryptography.ComputationalProblems.Games.Abstract.Macro where

import           Types

import           Macro.MetaMacro

import           Functions.Application.Macro
import           Logic.PropositionalLogic.Macro

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
