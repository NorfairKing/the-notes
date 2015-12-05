module Sets.Main (sets) where

import           Notes

import           Sets.Algebra.Main
import           Sets.Basics            (setBasics)
import           Sets.CarthesianProduct
import           Sets.Partition
import           Sets.Powerset

sets :: Notes
sets = notes "sets" $
  [
    header
  , setBasics
  , partitions
  , algebra
  , powerset
  , carthesianProducts
  ]

header :: Notes
header = notesPart "header" (chapter "Sets")
