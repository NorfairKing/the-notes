module Sets.Partition where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Sets.Basics.Terms

makeDefs ["partition"]

partitions :: Note
partitions = note "partition" $ do
    partitionDefinition

partitionDefinition :: Note
partitionDefinition = de $ do
    s ["A ", partition', " is a ", set, " ", m bb, " of subsets of a set ", m a, " with the following properties"]
    enumerate $ do
        item $ m $ emptyset `nin` bb
        item $ m $ setuncmp (b ∈ bb) b =: a
        item $ m $ fa (cs [b1, b2] ∈ bb) $ (b1 =§/= b2) ⇒ ((b1 ∩ b2) =§= emptyset)
  where
    a = "A"
    b = "b"
    b1 = b !: 1
    b2 = b !: 2
    bb = "B"

