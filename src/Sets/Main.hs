module Sets.Main where

import           Notes

import           Sets.Algebra.Main
import           Sets.Basics
import           Sets.CarthesianProduct
import           Sets.Multiset
import           Sets.Partition
import           Sets.PointedSets
import           Sets.Powerset

sets :: Note
sets = chapter "Sets" $ do
    setBasics
    partitionS
    algebra
    powersetS
    carthesianProducts
    pointedSets
    multisetS

