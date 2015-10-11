module Logic.Main (logic) where

import           Notes

import           Logic.AbstractLogic
import           Logic.HoareLogic
import           Logic.PropositionalLogic


logic :: Notes
logic = notes "logic"
  [
    logicHeader
  , abstractLogic
  , propositionalLogic
  , hoareLogic
  ]

logicHeader :: Notes
logicHeader = notesPart "header" (chapter "Logic")
