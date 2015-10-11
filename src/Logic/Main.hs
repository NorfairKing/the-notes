module Logic.Main (logic) where

import           Logic.AbstractLogic
import           Logic.PropositionalLogic
import           Notes


logic :: Notes
logic = notes "logic"
  [
    logicHeader
  , abstractLogic
  , propositionalLogic
  ]

logicHeader :: Notes
logicHeader = notesPart "header" (chapter "Logic")
