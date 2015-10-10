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
  section "The algebra of sets"
  setUnion
  setIntersection
  complement
  difference

setUnion :: Note
setUnion = do
  subsection "Set union"
  unionDefinition
  unionCommutative
  unionIdempotent
  unionSupset
  unionSubsetDefinition

setIntersection :: Note
setIntersection = do
  subsection "Set intersection"
  intersectionDefinition
  intersectionCommutative
  intersectionIdempotent
  intersectionSubset
  intersectionSubsetDefinition

complement :: Note
complement = do
  subsection "Set complement"

difference :: Note
difference = do
  subsection "Set difference"

a, b, x, y :: Note
a = "A"
b = "B"
x = "x"
y = "y"

union :: Note
union = ix "union"

unionDefinition :: Note
unionDefinition = de $ do
  s ["The ", term "union", " ", m (a `setun` b), " of two sets ", m a, " and ", m b, " is the set of all elements of both ", m a, " and ", m b, "."]
  ma $ a ∪ b =§= setcmpr x ((x ∈ a) |: (x ∈ b))

unionCommutative :: Note
unionCommutative = prop $ do
  s ["The set ", union, " is ", "commutative", "."]
  ma $ a ∪ b =§= b ∪ a

  proof $ do
    m $ a ∪ b
        =§= setcmpr x ((x ∈ a) |: (x ∈ b))
        =§= setcmpr x ((x ∈ b) |: (x ∈ a))
        =§= b ∪ a

unionIdempotent :: Note
unionIdempotent = prop $ do
  s ["The set ", union, " is ", ix "idempotent" ,"."]
  ma $ a ∪ a =§= a

  proof $ do
    m $ a ∪ a
        =§= setcmpr x ((x ∈ a) |: (x ∈ a))
        =§= setcmpr x (x ∈ a)
        =§= a

unionSupset :: Note
unionSupset = thm $ do
  s ["The set ", union, " of two sets ", m a, " and ", m b, " is a superset of ", m a, "."]
  
  ma $ a ⊆ a ∪ b

  proof $ do 
    m $ a
        =§= setcmpr x (x ∈ a)
        ⊆ setcmpr x ((x ∈ a) |: (x ∈ b))
        =§= a ∪ b

unionSubsetDefinition :: Note
unionSubsetDefinition = thm $ do
  ma $ a ⊆ b ⇔ (a ∪ b =§= a)

  proof $ do
    s ["Let ", m b, " be a set and ", m a, " a subset of ", m b, "."]
    ma $ a ∪ b
        =§= setcmpr x ((x ∈ a) |: (x ∈ b))
        =§= setcmpr x (x ∈ a)


intersectionDefinition :: Note
intersectionDefinition = de $ do
  s ["The ", term "intersection", " ", m (a ∪ b), " of two sets ", m a, " and ", m b, " is the set of all elements of both ", m a, " and ", m b, "."]
  ma $ a ∪ b =§= setcmpr x ((x ∈ a) &: (x ∈ b))

intersection :: Note
intersection = ix "intersection"

intersectionCommutative :: Note
intersectionCommutative = prop $ do
  s ["The set ", intersection, " is ", ix "commutative", "."]
  ma $ a ∩ b =§= b ∩ a

  proof $ do
    m $ a ∩ b
        =§= setcmpr x ((x ∈ a) &: (x ∈ b))
        =§= setcmpr x ((x ∈ b) &: (x ∈ a))
        =§= b ∩ a

intersectionIdempotent :: Note
intersectionIdempotent = prop $ do
  s ["The set ", intersection, " is ", ix "idempotent" ,"."]
  ma $ a ∩ a =§= a

  proof $ do
    m $ a ∩ a
        =§= setcmpr x ((x ∈ a) &: (x ∈ a))
        =§= setcmpr x (x ∈ a)
        =§= a

intersectionSubset :: Note
intersectionSubset = thm $ do
  s ["The set ", intersection, " of two sets ", m a, " and ", m b, " is a subset of ", m a, "."]
  ma $ a ∩ b ⊆ a

  proof $ do 
    m $ a ∩ b
        =§= setcmpr x ((x ∈ a) &: (x ∈ b))
        ⊆ setcmpr x (x ∈ a)
        =§= a

intersectionSubsetDefinition :: Note
intersectionSubsetDefinition = thm $ do
  ma $ a ⊆ b ⇔ (a ∩ b =§= b)

  proof $ do
    s ["Let ", m b, " be a set and ", m a, " a subset of ", m b, "."]

    ma $ a ∩ b
        =§= setcmpr x ((x ∈ a) &: (x ∈ b))
        =§= setcmpr x (x ∈ b)
        =§= b
        


secondLawOfDeMorganLabel :: Note
secondLawOfDeMorganLabel = "thm:second-law-of-de-morgan"

symmetricDifferenceITOUnionAndIntersectionLabel :: Note
symmetricDifferenceITOUnionAndIntersectionLabel = "thm:sets-symmetric-difference-in-terms-of-union-and-intersection"

unionComplementaryLawLabel :: Note
unionComplementaryLawLabel = "thm:complementary-law-union"

setDifferenceEquivalentDefinitionLabel :: Note
setDifferenceEquivalentDefinitionLabel = "thm:set-difference-equivalent-definition"
