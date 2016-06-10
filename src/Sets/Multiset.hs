module Sets.Multiset where

import           Notes

import           Sets.Basics.Terms

import           Sets.Multiset.Macro
import           Sets.Multiset.Terms


multisetS :: Note
multisetS = section "Multisets" $ do
    multisetDefinition
    multisetNotation
    exneeded
    multisetDifferenceDefinition
    multisetUnionDefinition

multisetDefinition :: Note
multisetDefinition = de $ do
    lab multisetDefinitionLabel
    s ["A", multiset', "is a", set, "of", elements, "each imbued with a", multiplicity']

multisetNotation :: Note
multisetNotation = nte $ do
    s ["Instead of stating an explicit", multiplicity, "we may also simply write", elements, "multiple times in the same set notation"]

multisetDifferenceDefinition :: Note
multisetDifferenceDefinition = de $ do
    let a = "A"
        b = "B"
    s [the, multiset, "union", "of two", multisets, m a, and, m b, "is defined as the", multiset, m $ a `msetun` b, "where the", elements, "are in the union of the underlying", sets, "and the", multiplicities, "are the sum of", multiplicities, "in the", multisets, m a, and, m b]

multisetUnionDefinition :: Note
multisetUnionDefinition = de $ do
    let a = "A"
        b = "B"
    s [the, multiset, "difference", "of two", multisets, m a, and, m b, "is defined as the", multiset, m $ a `msetdiff` b, "where the", elements, "are in the difference of the underlying", sets, "and the", multiplicities, "are the difference of", multiplicities, "in the", multisets, m a, and, m b]
