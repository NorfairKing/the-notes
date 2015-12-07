module Logic.Main (logica) where

import           Notes

import           Logic.AbstractLogic      (abstractLogic)
import           Logic.FirstOrderLogic
import           Logic.HoareLogic         (hoareLogicS)
import           Logic.PropositionalLogic


logica :: Notes
logica = notes "logic"
  [
    logicHeader
  , abstractLogic
  , propositionalLogic
  , firstOrderLogic
  , hoareLogicS
  ]

logicHeader :: Notes
logicHeader = notesPart "header" (chapter "Logic")
