module Sets.Algebra.Intersection (setIntersection, intersection) where

import           Notes

intersection :: Note
intersection = ix "intersection"

setIntersection :: Notes
setIntersection = notesPart "intersection" body

body :: Note
body = do
  subsection "Set intersection"
  intersectionDefinition
  intersectionAssociative
  intersectionCommutative
  intersectionIdempotent
  intersectionSubset
  intersectionSubsetDefinition
  intersectionIdentityLaw


a, b, c, x, y :: Note
a = "A"
b = "B"
c = "C"
x = "x"
y = "y"

intersectionDefinition :: Note
intersectionDefinition = de $ do
  s ["The ", term "intersection", " ", m (a ∪ b), " of two sets ", m a, " and ", m b, " is the set of all elements of both ", m a, " and ", m b, "."]
  ma $ a ∪ b =§= setcmpr x ((x ∈ a) &: (x ∈ b))

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


