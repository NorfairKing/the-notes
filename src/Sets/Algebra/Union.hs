module Sets.Algebra.Union where

import           Notes

import           Logic.PropositionalLogic.Macro
import           Sets.Basics                    (set)

import           Functions.BinaryOperation      (associative_)

makeDef "union"

setUnion :: Note
setUnion = note "union" $ do
    subsection "Set union"
    unionDefinition
    unionAssociative
    unionCommutative
    unionIdempotent
    unionSupset
    unionSubsetDefinition
    unionIdentityLaw
    unionDominationLaw

a, b, c, x, y :: Note
a = "A"
b = "B"
c = "C"
x = "x"
y = "y"

unionDefinition :: Note
unionDefinition = de $ do
  lab unionDefinitionLabel
  s [the, union', " ", m (a `setun` b), " of two sets ", m a, " and ", m b, " is the set of all elements of both ", m a, " and ", m b]
  ma $ a ∪ b =§= setcmpr x ((x ∈ a) ∨ (x ∈ b))

unionAssociative :: Note
unionAssociative = prop $ do
  s [the, set, " ", union, " is ", associative_]
  ma $ a ∪ (pars $ b ∪ c) =§= (pars $ a ∪ b) ∪ c

  proof $ do
    align_ $
      [
        a ∪ (pars $ b ∪ c)
        & "" =§= setcmpr x ((x ∈ a) ∨ (x ∈ (pars $ b ∪ c)))
        , "" & "" =§= setcmpr x (x ∈ a) ∨ x ∈ setcmpr y ((y ∈ b) ∨ (y ∈ c))
        , "" & "" =§= setcmpr x ((x ∈ a) ∨ (x ∈ b)) ∨ (y ∈ c)
        , "" & "" =§= setcmpr x (x ∈ setcmpr y ((y ∈ a) ∨ (y ∈ b))) ∨ (x ∈ c)
        , "" & "" =§= setcmpr x (x ∈ (pars $ a ∪ b)) ∨ (x ∈ c)
        , "" & "" =§= (pars $ a ∪ b) ∪ c
      ]

unionCommutative :: Note
unionCommutative = prop $ do
  s ["The ", set, " ", union, " is ", commutative]
  ma $ a ∪ b =§= b ∪ a

  proof $ do
    m $ a ∪ b
        =§= setcmpr x ((x ∈ a) ∨ (x ∈ b))
        =§= setcmpr x ((x ∈ b) ∨ (x ∈ a))
        =§= b ∪ a

unionIdempotent :: Note
unionIdempotent = prop $ do
  s ["The ", set, " ", union, " is ", idempotent ,""]
  ma $ a ∪ a =§= a

  proof $ do
    m $ a ∪ a
        =§= setcmpr x ((x ∈ a) ∨ (x ∈ a))
        =§= setcmpr x (x ∈ a)
        =§= a


unionSupset :: Note
unionSupset = thm $ do
  s ["The ", set, " ", union, " of two sets ", m a, and, m b, " is a superset of ", m a]

  ma $ a ⊆ a ∪ b

  proof $ do
    m $ a
        =§= setcmpr x (x ∈ a)
        ⊆ setcmpr x ((x ∈ a) ∨ (x ∈ b))
        =§= a ∪ b

unionSubsetDefinition :: Note
unionSubsetDefinition = thm $ do
  ma $ a ⊆ b ⇔ (a ∪ b =§= a)

  proof $ do
    s ["Let ", m b, " be a set and ", m a, " a subset of ", m b]
    ma $ a ∪ b
        =§= setcmpr x ((x ∈ a) ∨ (x ∈ b))
        =§= setcmpr x (x ∈ a)

unionIdentityLaw :: Note
unionIdentityLaw = thm $ do
  s [the, term "identity law", " for the ", set, " ", union]
  ma $ a ∪ emptyset =§= a

  proof $ do
    m $ a ∪ emptyset
        =§= setcmpr x ((x ∈ a) ∨ (x ∈ emptyset))
        =§= setcmpr x ((x ∈ a) ∨ false)
        =§= setcmpr x (x ∈ a)
        =§= a

unionDominationLaw :: Note
unionDominationLaw = thm $ do
  s [the, term "domination law", " for the ", set, " ", union]
  ma $ a ∪ setuniv =§= setuniv

  proof $ do
    m $ a ∪ setuniv
        =§= setcmpr x ((x ∈ a) ∨ (x ∈ setuniv))
        =§= setcmpr x ((x ∈ a) ∨ true)
        =§= setcmpr x true
        =§= setuniv
