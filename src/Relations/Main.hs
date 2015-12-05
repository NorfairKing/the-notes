module Relations.Main (relations) where

import           Notes

import           Relations.Basics
import           Relations.Equivalence
import           Relations.Orders      (orders)


relations :: Notes
relations = notes "relations"
  [
    notesPart "header" (chapter "Relations")
  , relationBasics
  , equivalenceRelations
  , orders
  ]


