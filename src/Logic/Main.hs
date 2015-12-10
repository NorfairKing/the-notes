module Logic.Main (logica) where

import           Notes

import           Logic.AbstractLogic      (abstractLogic)
import           Logic.FirstOrderLogic
import           Logic.HoareLogic         (hoareLogicS)
import           Logic.PropositionalLogic
import           Logic.SeparationLogic    (separationLogicS)


logica :: Notes
logica = notes "logic"
  [
    logicHeader
  , abstractLogic
  , propositionalLogic
  , firstOrderLogic
  , hoareLogicS
  , separationLogicS
  ]

logicHeader :: Notes
logicHeader = notesPart "header" (chapter "Logic")
