module Sets.Algebra (
    algebra

  , secondLawOfDeMorganLabel
  , symmetricDifferenceITOUnionAndIntersectionLabel
  ) where

import           Notes

algebra :: Notes
algebra = notesPart "algebra" body

body :: Note
body = do
  union
  intersection
  complement
  difference

union :: Note
union = do
  unionDefinition

intersection :: Note
intersection = return ()

complement :: Note
complement = return ()

difference :: Note
difference = return ()

unionDefinition :: Note
unionDefinition = do
  s ["The ", term "union", " ", m ("A" `setun` "B"), " of two sets ", m "A", " and ", m "B", " is the set of all elements of both ", m "A", " and ", m "B", "."]
  ma $ "A" `setun` "B" =§= setcmpr "x" (("x" ∈ "A") |: ("x" ∈ "B"))

secondLawOfDeMorganLabel :: Note
secondLawOfDeMorganLabel = "thm:second-law-of-de-morgan"

symmetricDifferenceITOUnionAndIntersectionLabel :: Note
symmetricDifferenceITOUnionAndIntersectionLabel = "thm:sets-symmetric-difference-in-terms-of-union-and-intersection"
