module Logic.Main (logica) where

import           Notes

import           Logic.AbstractLogic      (abstractLogic)
import           Logic.FirstOrderLogic
import           Logic.HoareLogic         (hoareLogicS)
import           Logic.PropositionalLogic (propositionalLogicS)
import           Logic.SeparationLogic    (separationLogicS)
import           Logic.TemporalLogic      (temporalLogicS)


logica :: Notes
logica = notes "logic"
  [
    logicHeader
  , abstractLogic
  , propositionalLogicS
  , firstOrderLogic
  , hoareLogicS
  , separationLogicS
  , temporalLogicS
  ]

logicHeader :: Notes
logicHeader = notesPart "header" (chapter "Logic")
