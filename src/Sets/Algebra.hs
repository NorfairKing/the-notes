module Sets.Algebra (
    algebra

  , secondLawOfDeMorganLabel
  , symmetricDifferenceITOUnionAndIntersectionLabel
  , unionComplementaryLawLabel
  , setDifferenceEquivalentDefinitionLabel
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
intersection = do
  intersectionDefinition

complement :: Note
complement = return ()

difference :: Note
difference = return ()

a, b, x, y :: Note
a = "A"
b = "B"
x = "x"
y = "y"

unionDefinition :: Note
unionDefinition = de $ do
  s ["The ", term "union", " ", m (a `setun` b), " of two sets ", m a, " and ", m b, " is the set of all elements of both ", m a, " and ", m b, "."]
  ma $ a `setun` b =§= setcmpr x ((x ∈ a) |: (x ∈ b))

intersectionDefinition :: Note
intersectionDefinition = de $ do
  s ["The ", term "intersection", " ", m (a ∪ b), " of two sets ", m a, " and ", m b, " is the set of all elements of both ", m a, " and ", m b, "."]
  ma $ a ∪ b =§= setcmpr x ((x ∈ a) &: (x ∈ b))

secondLawOfDeMorganLabel :: Note
secondLawOfDeMorganLabel = "thm:second-law-of-de-morgan"

symmetricDifferenceITOUnionAndIntersectionLabel :: Note
symmetricDifferenceITOUnionAndIntersectionLabel = "thm:sets-symmetric-difference-in-terms-of-union-and-intersection"

unionComplementaryLawLabel :: Note
unionComplementaryLawLabel = "thm:complementary-law-union"

setDifferenceEquivalentDefinitionLabel :: Note
setDifferenceEquivalentDefinitionLabel = "thm:set-difference-equivalent-definition"
