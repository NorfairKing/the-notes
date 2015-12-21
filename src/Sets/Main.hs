module Sets.Main where

import           Notes

import           Sets.Algebra.Main
import           Sets.Basics            (setBasics)
import           Sets.CarthesianProduct
import           Sets.Partition
import           Sets.PointedSets       (pointedSets)
import           Sets.Powerset

sets :: Note
sets = note "sets" $ do
     chapter "Sets"
     setBasics
     partitions
     algebra
     powerset
     carthesianProducts
     pointedSets

