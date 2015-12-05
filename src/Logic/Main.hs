module Logic.Main (logica) where

import           Notes

import           Logic.AbstractLogic      (abstractLogic)
import           Logic.FirstOrderLogic
import           Logic.HoareLogic
import           Logic.PropositionalLogic


logica :: Notes
logica = notes "logic"
  [
    logicHeader
  , abstractLogic
  , propositionalLogic
  , firstOrderLogic
  , hoareLogic
  ]

logicHeader :: Notes
logicHeader = notesPart "header" (chapter "Logic")
