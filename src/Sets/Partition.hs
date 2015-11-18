module Sets.Partition (
      partitions

    , partition     , partition_
    ) where

import           Notes

import           Sets.Basics (set)

makeDefs ["partition"]

partitions :: Notes
partitions = notesPart "partition" body

body :: Note
body = do
    partitionDefinition

partitionDefinition :: Note
partitionDefinition = de $ do
    s ["A ", partition', " is a ", set, " ", m bb, " of subsets of a set ", m a, " with the following properties"]
    enumerate $ do
        item $ m $ emptyset ∈ bb
        item $ m $ setuncmp (b ∈ bb) b =: a
        item $ m $ fa (cs [b1, b2] ∈ bb) $ (b1 =§/= b2) ⇒ ((b1 ∩ b2) =§= emptyset)
  where
    a = "A"
    b = "b"
    b1 = b !: 1
    b2 = b !: 2
    bb = "B"

