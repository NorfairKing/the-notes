module Sets.Algebra.Main where

import           Notes

import           Sets.Algebra.Complement
import           Sets.Algebra.Difference
import           Sets.Algebra.Intersection
import           Sets.Algebra.Union


algebra :: Note
algebra = section "The algebra of sets" $ do
    setUnion
    setIntersection
    setDifference
    setComplement

