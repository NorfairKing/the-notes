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
  difference
  complement

setUnion :: Note
setUnion = do
  subsection "Set union"
  unionDefinition
  unionAssociative
  unionCommutative
  unionIdempotent
  unionSupset
  unionSubsetDefinition
  unionIdentityLaw

setIntersection :: Note
setIntersection = do
  subsection "Set intersection"
  intersectionDefinition
  intersectionAssociative
  intersectionCommutative
  intersectionIdempotent
  intersectionSubset
  intersectionSubsetDefinition
  intersectionIdentityLaw

complement :: Note
complement = do
  subsection "Set complement"
  complementDefinition

difference :: Note
difference = do
  subsection "Set difference"


a, b, x, y :: Note
a = "A"
b = "B"
c = "C"
x = "x"
y = "y"

union :: Note
union = ix "union"

unionDefinition :: Note
unionDefinition = de $ do
  s ["The ", term "union", " ", m (a `setun` b), " of two sets ", m a, " and ", m b, " is the set of all elements of both ", m a, " and ", m b, "."]
  ma $ a ∪ b =§= setcmpr x ((x ∈ a) |: (x ∈ b))

unionAssociative :: Note
unionAssociative = prop $ do
  s ["The set ", union, " is ", associative, "."]
  ma $ a ∪ (pars $ b ∪ c) =§= (pars $ a ∪ b) ∪ c

  proof $ do
    align_ $
      [
        a ∪ (pars $ b ∪ c)
        & "" =§= setcmpr x ((x ∈ a) |: (x ∈ (pars $ b ∪ c)))
        , "" & "" =§= setcmpr x ((x ∈ a) |: (x ∈ (setcmpr y ((y ∈ b) |: (y ∈ c)))))
        , "" & "" =§= setcmpr x ((x ∈ a) |: (x ∈ b) |: (y ∈ c))
        , "" & "" =§= setcmpr x ((x ∈ (setcmpr y ((y ∈ a) |: (y ∈ b)))) |: (x ∈ c))
        , "" & "" =§= setcmpr x ((x ∈ (pars $ a ∪ b)) |: (x ∈ c))
        , "" & "" =§= (pars $ a ∪ b) ∪ c
      ]

unionCommutative :: Note
unionCommutative = prop $ do
  s ["The set ", union, " is ", commutative, "."]
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

unionIdentityLaw :: Note
unionIdentityLaw = thm $ do
  s ["The ", term "identity law", " for the set union."]
  ma $ a ∪ emptyset =§= a

  proof $ do
    m $ a ∪ emptyset
        =§= setcmpr x ((x ∈ a) |: (x ∈ emptyset))
        =§= setcmpr x ((x ∈ a) |: false)
        =§= setcmpr x (x ∈ a)
        =§= a



intersectionDefinition :: Note
intersectionDefinition = de $ do
  s ["The ", term "intersection", " ", m (a ∪ b), " of two sets ", m a, " and ", m b, " is the set of all elements of both ", m a, " and ", m b, "."]
  ma $ a ∪ b =§= setcmpr x ((x ∈ a) &: (x ∈ b))

intersection :: Note
intersection = ix "intersection"

intersectionAssociative :: Note
intersectionAssociative = prop $ do
  s ["The set ", intersection, " is ", associative, "."]
  ma $ a ∩ (pars $ b ∩ c) =§= (pars $ a ∩ b) ∩ c

  proof $ do
    align_ $
      [
        a ∩ (pars $ b ∩ c)
        & "" =§= setcmpr x ((x ∈ a) &: (x ∈ (pars $ b ∩ c)))
        , "" & "" =§= setcmpr x ((x ∈ a) &: (x ∈ (setcmpr y ((y ∈ b) &: (y ∈ c)))))
        , "" & "" =§= setcmpr x ((x ∈ a) &: (x ∈ b) &: (y ∈ c))
        , "" & "" =§= setcmpr x ((x ∈ (setcmpr y ((y ∈ a) &: (y ∈ b)))) &: (x ∈ c))
        , "" & "" =§= setcmpr x ((x ∈ (pars $ a ∩ b)) &: (x ∈ c))
        , "" & "" =§= (pars $ a ∩ b) ∩ c
      ]

intersectionCommutative :: Note
intersectionCommutative = prop $ do
  s ["The set ", intersection, " is ", commutative, "."]
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

intersectionIdentityLaw :: Note
intersectionIdentityLaw = thm $ do
  s ["The ", term "identity law", " for the set ", intersection, "."]
  ma $ a ∩ setuniv =§= a

  proof $ do
    m $ a ∩ emptyset
        =§= setcmpr x ((x ∈ a) &: (x ∈ setuniv))
        =§= setcmpr x ((x ∈ a) &: true)
        =§= setcmpr x (x ∈ a)
        =§= a

complementDefinition :: Note
complementDefinition = de $ do
  s ["The ", term "comlement", " of a set ", m a, " relative to a set ", m b, " is the set of all elements of ", m b, " that are not in ", m a, "."]


secondLawOfDeMorganLabel :: Note
secondLawOfDeMorganLabel = "thm:second-law-of-de-morgan"

symmetricDifferenceITOUnionAndIntersectionLabel :: Note
symmetricDifferenceITOUnionAndIntersectionLabel = "thm:sets-symmetric-difference-in-terms-of-union-and-intersection"

unionComplementaryLawLabel :: Note
unionComplementaryLawLabel = "thm:complementary-law-union"

setDifferenceEquivalentDefinitionLabel :: Note
setDifferenceEquivalentDefinitionLabel = "thm:set-difference-equivalent-definition"
