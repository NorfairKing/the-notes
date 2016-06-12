module Cryptography.ComputationalProblems.Games.HardnessAmplification.Macro where

import           Types

import           Macro.Math

import           Logic.PropositionalLogic.Macro

andgames :: Note -> Note
andgames = (^ ("" ∧ "")) . sqbrac

andgamelist :: Note -> Note -> Note -> Note
andgamelist n1 n2 nk = andgames $ list n1 n2 nk
