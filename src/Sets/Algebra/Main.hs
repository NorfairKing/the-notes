module Sets.Algebra.Main (
    algebra

  , secondLawOfDeMorganLabel
  , symmetricDifferenceITOUnionAndIntersectionLabel
  , unionComplementaryLawLabel
  , setDifferenceEquivalentDefinitionLabel
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

secondLawOfDeMorganLabel :: Label
secondLawOfDeMorganLabel = thmlab "second-law-of-de-morgan"

symmetricDifferenceITOUnionAndIntersectionLabel :: Label
symmetricDifferenceITOUnionAndIntersectionLabel = thmlab "sets-symmetric-difference-in-terms-of-union-and-intersection"

setDifferenceEquivalentDefinitionLabel :: Label
setDifferenceEquivalentDefinitionLabel = thmlab "set-difference-equivalent-definition"
