module Sets.Main (sets) where

import           Notes

import           Sets.Algebra.Main
import           Sets.Basics            (setBasics)
import           Sets.CarthesianProduct
import           Sets.Partition
import           Sets.PointedSets       (pointedSets)
import           Sets.Powerset

sets :: Notes
sets = notes "sets" $
  [
    notesPart "header" (chapter "Sets")
  , setBasics
  , partitions
  , algebra
  , powerset
  , carthesianProducts
  , pointedSets
  ]
