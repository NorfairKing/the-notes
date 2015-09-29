module Sets.Main (sets) where

import           Notes

import           Sets.Algebra
import           Sets.Basics
import           Sets.CarthesianProduct
import           Sets.Powerset

sets :: Notes
sets = notes "sets" $
  [
    header
  , basics
  , algebra
  , powerset
  , carthesianProduct
  ]

header :: Notes
header = notesPart "header" (chapter "Sets")
