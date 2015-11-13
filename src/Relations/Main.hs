module Relations.Main (relations) where

import           Notes

import           Relations.Basics
import           Relations.Equivalence



relations :: Notes
relations = notes "relations"
  [
    notesPart "header" (chapter "Relations")
  , relationBasics
  , equivalenceRelations
  ]


