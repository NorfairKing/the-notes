module Sets.Main where

import           Notes

import           Sets.Algebra.Main
import           Sets.Basics
import           Sets.CarthesianProduct
import           Sets.Partition
import           Sets.PointedSets
import           Sets.Powerset

sets :: Note
sets = chapter "Sets" $ do
     setBasics
     partitions
     algebra
     powersetS
     carthesianProducts
     pointedSets

