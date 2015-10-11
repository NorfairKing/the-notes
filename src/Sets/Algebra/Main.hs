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

secondLawOfDeMorganLabel :: Note
secondLawOfDeMorganLabel = "thm:second-law-of-de-morgan"

symmetricDifferenceITOUnionAndIntersectionLabel :: Note
symmetricDifferenceITOUnionAndIntersectionLabel = "thm:sets-symmetric-difference-in-terms-of-union-and-intersection"

unionComplementaryLawLabel :: Note
unionComplementaryLawLabel = "thm:complementary-law-union"

setDifferenceEquivalentDefinitionLabel :: Note
setDifferenceEquivalentDefinitionLabel = "thm:set-difference-equivalent-definition"
