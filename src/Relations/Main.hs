module Relations.Main (relations) where

import           Notes

import           Relations.Basics
import           Relations.Equivalence (equivalenceRelations)
import           Relations.Orders      (orders)
import           Relations.Preorders   (preorders)


relations :: Notes
relations = notes "relations"
  [
    notesPart "header" (chapter "Relations")
  , relationBasics
  , preorders
  , equivalenceRelations
  , orders
  ]


