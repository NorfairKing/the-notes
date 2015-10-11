module Sets.Algebra.Main (
    algebra

  , symmetricDifferenceITOUnionAndIntersectionLabel
  , unionComplementaryLawLabel
  , setDifferenceEquivalentDefinitionLabel
  , firstLawOfDeMorganLabel
  , secondLawOfDeMorganLabel
  ) where

import           Notes

import           Sets.Algebra.Complement
import           Sets.Algebra.Difference
import           Sets.Algebra.Intersection
import           Sets.Algebra.Union


algebra :: Notes
algebra = notes "algebra" $
  [
    notesPart "header" (section "The algebra of sets")
  , setUnion
  , setIntersection
  , setDifference
  , setComplement
  ]

symmetricDifferenceITOUnionAndIntersectionLabel :: Label
symmetricDifferenceITOUnionAndIntersectionLabel = thmlab "sets-symmetric-difference-in-terms-of-union-and-intersection"

setDifferenceEquivalentDefinitionLabel :: Label
setDifferenceEquivalentDefinitionLabel = thmlab "set-difference-equivalent-definition"
