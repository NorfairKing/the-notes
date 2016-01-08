module Sets.Algebra.Intersection where

import           Notes

import           Functions.BinaryOperation.Terms
import           Logic.PropositionalLogic.Macro

import           Sets.Algebra.Union.Terms

import           Sets.Algebra.Intersection.Terms

setIntersection :: Note
setIntersection = note "intersection" $ do
    subsection "Set intersection"
    intersectionDefinition
    intersectionAssociative
    intersectionCommutative
    intersectionIdempotent
    intersectionSubset
    intersectionSubsetDefinition
    intersectionIdentityLaw
    intersectionDominationLaw
    disjunctDefinition
    absorptionLaws
    distributionLaws


a, b, c, x, y :: Note
a = "A"
b = "B"
c = "C"
x = "x"
y = "y"

intersectionDefinition :: Note
intersectionDefinition = de $ do
    s [the, intersection', " ", m (a ∪ b), " of two sets ", m a, " and ", m b, " is the set of all elements of both ", m a, " and ", m b]
    ma $ a ∪ b =§= setcmpr x ((x ∈ a) ∧ (x ∈ b))

intersectionAssociativityLabel :: Label
intersectionAssociativityLabel = Label Property "intersection-associative"

intersectionAssociative :: Note
intersectionAssociative = prop $ do
    lab intersectionAssociativityLabel
    s ["The set ", intersection, " is ", associative_]
    ma $ a ∩ (pars $ b ∩ c) =§= (pars $ a ∩ b) ∩ c

    proof $ do
        align_ $
            [
              a ∩ (pars $ b ∩ c)
              & "" =§= setcmpr x ((x ∈ a) ∧ (x ∈ (pars $ b ∩ c)))
              , "" & "" =§= setcmpr x ((x ∈ a) ∧ (x ∈ setcmpr y ((y ∈ b) ∧ (y ∈ c))))
              , "" & "" =§= setcmpr x ((x ∈ a) ∧ (x ∈ b) ∧ (y ∈ c))
              , "" & "" =§= setcmpr x ((x ∈ setcmpr y ((y ∈ a) ∧ (y ∈ b))) ∧ (x ∈ c))
              , "" & "" =§= setcmpr x ((x ∈ (pars $ a ∩ b)) ∧ (x ∈ c))
              , "" & "" =§= (pars $ a ∩ b) ∩ c
            ]



intersectionCommutative :: Note
intersectionCommutative = prop $ do
    s ["The set ", intersection, " is ", commutative]
    ma $ a ∩ b =§= b ∩ a

    proof $ do
        m $ a ∩ b
            =§= setcmpr x ((x ∈ a) ∧ (x ∈ b))
            =§= setcmpr x ((x ∈ b) ∧ (x ∈ a))
            =§= b ∩ a

intersectionIdempotent :: Note
intersectionIdempotent = prop $ do
    s ["The set ", intersection, " is ", idempotent ,""]
    ma $ a ∩ a =§= a

    proof $ do
        m $ a ∩ a
            =§= setcmpr x ((x ∈ a) ∧ (x ∈ a))
            =§= setcmpr x (x ∈ a)
            =§= a

intersectionSubset :: Note
intersectionSubset = thm $ do
    s ["The set ", intersection, " of two sets ", m a, " and ", m b, " is a subset of ", m a]
    ma $ a ∩ b ⊆ a

    proof $ do
        m $ a ∩ b
            =§= setcmpr x ((x ∈ a) ∧ (x ∈ b))
            ⊆ setcmpr x (x ∈ a)
            =§= a

intersectionSubsetDefinition :: Note
intersectionSubsetDefinition = thm $ do
    ma $ a ⊆ b ⇔ (a ∩ b =§= b)

    proof $ do
        s ["Let ", m b, " be a set and ", m a, " a subset of ", m b]

        ma $ a ∩ b
            =§= setcmpr x ((x ∈ a) ∧ (x ∈ b))
            =§= setcmpr x (x ∈ b)
            =§= b


intersectionIdentityLaw :: Note
intersectionIdentityLaw = thm $ do
    s [the, term "identity law", " for the set ", intersection]
    ma $ a ∩ setuniv =§= a

    proof $ do
        m $ a ∩ emptyset
            =§= setcmpr x ((x ∈ a) ∧ (x ∈ setuniv))
            =§= setcmpr x ((x ∈ a) ∧ true)
            =§= setcmpr x (x ∈ a)
            =§= a

intersectionDominationLaw :: Note
intersectionDominationLaw = thm $ do
    s [the, term "domination law", " for the set ", intersection]
    ma $ a ∩ setuniv =§= a

    proof $ do
      m $ a ∩ setuniv
          =§= setcmpr x ((x ∈ a) ∧ (x ∈ setuniv))
          =§= setcmpr x ((x ∈ a) ∧ true)
          =§= setcmpr x (x ∈ a)
          =§= a


disjunctDefinition :: Note
disjunctDefinition = de $ do
    s ["Two sets ", m a, and, m b, " are ", term "disjunct", " if they have no elements in common"]
    ma $ a ∩ b =§= emptyset


absorptionLaws :: Note
absorptionLaws = do
    absorptionLaw1
    absorptionLaw2

absorptionLaw1 :: Note
absorptionLaw1 = thm $ do
    s ["The first ", term "absorption law"]
    ma $ a ∪ (pars $ a ∩ b) =§= a

    proof $ do
        align_ $
            [
              a ∪ (pars $ a ∩ b)
              & "" =§= setcmpr x ((x ∈ a) ∨ (x ∈ a ∩ b))
              , "" & "" =§= setcmpr x ((x ∈ a) ∨ (x ∈ setcmpr y ((y ∈ a) ∧ (y ∈ b))))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∧ (x ∈ a)) ∨ (pars $ (x ∈ a) ∧ (x ∈ b)))
              , "" & "" =§= setcmpr x ((x ∈ a) ∨ (pars $ (x ∈ a) ∧ (x ∈ b)))
              , "" & "" =§= setcmpr x (x ∈ a)
              , "" & "" =§= a
            ]


absorptionLaw2 :: Note
absorptionLaw2 = thm $ do
    s ["The second ", term "absorption law"]
    ma $ a ∩ (pars $ a ∪ b) =§= a

    proof $ do
        align_ $
            [
              a ∩ (pars $ a ∪ b)
              & "" =§= setcmpr x ((x ∈ a) ∧ (x ∈ a ∪ b))
              , "" & "" =§= setcmpr x ((x ∈ a) ∧ (x ∈ setcmpr y ((y ∈ a) ∨ (y ∈ b))))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∨ (x ∈ a)) ∧ (pars $ (x ∈ a) ∨ (x ∈ b)))
              , "" & "" =§= setcmpr x ((x ∈ a) ∧ (pars $ (x ∈ a) ∨ (x ∈ b)))
              , "" & "" =§= setcmpr x (x ∈ a)
              , "" & "" =§= a
            ]

distributionLaws :: Note
distributionLaws = do
    distributionLaw1
    distributionLaw2

distributionLaw1Label :: Label
distributionLaw1Label = Label Theorem "dristribution-law-1"

distributionLaw1 :: Note
distributionLaw1 = thm $ do
    lab distributionLaw1Label
    s ["The set ", intersection, is, distributive, " with respect to the set ", union]
    ma $ a ∩ (pars $ b ∪ c) =§= (pars $ a ∪ b) ∩ (pars $ a ∪ c)

    proof $ do
        align_ $
            [
              a ∩ (pars $ b ∪ c)
              & "" =§= setcmpr x ((x ∈ a) ∧ (x ∈ b ∪ c))
              , "" & "" =§= setcmpr x ((x ∈ a) ∧ setcmpr y ((y ∈ b) ∨ (y ∈ c)))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∨ (x ∈ b)) ∧ (pars $ (x ∈ a) ∨ (x ∈ c)))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∨ (x ∈ b)) ∧ (pars $ (x ∈ a) ∨ (x ∈ c)))
              , "" & "" =§= setcmpr x (x ∈ setcmpr y (pars $ (y ∈ a) ∨ (y ∈ b)) ∧ (x ∈ setcmpr y (pars $ (y ∈ a) ∨ (y ∈ c))))
              , "" & "" =§= setcmpr x (pars $ (x ∈ a) ∨ (x ∈ b)) ∩ setcmpr x (pars $ (x ∈ a) ∨ (x ∈ c))
              , "" & "" =§= (pars $ a ∪ b) ∩ (pars $ a ∪ c)
            ]

distributionLaw2Label :: Label
distributionLaw2Label = Label Theorem "dristribution-law-2"

distributionLaw2 :: Note
distributionLaw2 = thm $ do
    lab distributionLaw2Label
    s ["The set ", union, is, distributive, " with respect to the set ", intersection]
    ma $ a ∪ (pars $ b ∩ c) =§= (pars $ a ∩ b) ∪ (pars $ a ∩ c)

    proof $ do
        align_ $
            [
              a ∪ (pars $ b ∩ c)
              & "" =§= setcmpr x ((x ∈ a) ∨ (x ∈ b ∩ c))
              , "" & "" =§= setcmpr x ((x ∈ a) ∨ setcmpr y ((y ∈ b) ∧ (y ∈ c)))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∧ (x ∈ b)) ∨ (pars $ (x ∈ a) ∧ (x ∈ c)))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∧ (x ∈ b)) ∨ (pars $ (x ∈ a) ∧ (x ∈ c)))
              , "" & "" =§= setcmpr x (x ∈ setcmpr y (pars $ (y ∈ a) ∧ (y ∈ b)) ∨ (x ∈ setcmpr y (pars $ (y ∈ a) ∧ (y ∈ c))))
              , "" & "" =§= setcmpr x (pars $ (x ∈ a) ∧ (x ∈ b)) ∪ setcmpr x (pars $ (x ∈ a) ∧ (x ∈ c))
              , "" & "" =§= (pars $ a ∩ b) ∪ (pars $ a ∩ c)
            ]
