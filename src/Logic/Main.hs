module Logic.Main (logic) where

import           Notes

import           Logic.AbstractLogic
import           Logic.FirstOrderLogic
import           Logic.HoareLogic
import           Logic.PropositionalLogic


logic :: Notes
logic = notes "logic"
  [
    logicHeader
  , abstractLogic
  , propositionalLogic
  , firstOrderLogic
  , hoareLogic
  ]

logicHeader :: Notes
logicHeader = notesPart "header" (chapter "Logic")
