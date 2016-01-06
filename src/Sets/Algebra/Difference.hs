module Sets.Algebra.Difference where

import           Notes

import           Logic.PropositionalLogic.Macro

import           Sets.Algebra.Difference.Terms


setDifference :: Note
setDifference = note "difference" $ do
    subsection "Set difference"

    differenceDefinition
    intersectionAndDifferenceDisjunct
    symmetricSetDifferencesDisjunct

    symmetricDifferenceDefinition
    symmetricDifferenceEquivalentDefinition
    symmetricDifferenceITOUnionAndIntersection

    intersectionOverDifference


differenceDefinition :: Note
differenceDefinition = de $ do
    let (a, b, x) = ("A", "B", "x")
    s ["The set ", difference', " between sets ", m a, and, m b, " is the set of all elements of ", m a, " that are not in ", m b]
    ma $ a \\ b === setcmpr x ((x ∈ a) ∧ (x `nin` b))

setsDec :: Note
setsDec = do
    let (a, b) = ("A", "B")
    s ["Let ", m a, and, m b, " be sets"]

setssDec :: Note
setssDec = do
    let (a, b, c) = ("A", "B", "C")
    s ["Let ", m a, ", ", m b, and, m c, " be sets"]

intersectionAndDifferenceDisjunct :: Note
intersectionAndDifferenceDisjunct = thm $ do
    setsDec
    let (a, b, x, y) = ("A", "B", "x", "y")
    ma $ ((pars $ a ∩ b) ∩ (pars $ a \\ b)) =§= emptyset

    proof $ do
        align_ $
            [
              (pars $ a ∩ b) ∩ (pars $ a \\ b)
              & "" =§= setcmpr x ((x ∈ a) ∧ (x ∈ b)) ∩ setcmpr x ((x ∈ a) ∧ (x `nin` b))
              , "" & "" =§= setcmpr x (x ∈ setcmpr y ((y ∈ a) ∧ (y ∈ b)) ∧ x ∈ (setcmpr y (y ∈ a) ∧ (y `nin` b)))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∧ (x ∈ b)) ∧ (pars $ (x ∈ a) ∧ (x `nin` b)))
              , "" & "" =§= setcmpr x ((x ∈ a) ∧ (x ∈ b) ∧ (x `nin` b))
              , "" & "" =§= setcmpr x ((x ∈ a) ∧ false)
              , "" & "" =§= setcmpr x false
              , "" & "" =§= emptyset
            ]

symmetricSetDifferencesDisjunct :: Note
symmetricSetDifferencesDisjunct = thm $ do
    setsDec
    let (a, b, x, y) = ("A", "B", "x", "y")
    ma $ ((pars $ a \\ b) ∩ (pars $ b \\ a)) =§= emptyset

    proof $ do
        align_ $
            [
              (pars $ a \\ b) ∩ (pars $ b \\ a)
              & "" =§= setcmpr x ((x ∈ a) ∧ (x `nin` b)) ∩ setcmpr x ((x ∈ b) ∧ (x `nin` a))
              , "" & "" =§= setcmpr x (x ∈ setcmpr y ((y ∈ a) ∧ (y `nin` b)) ∧ x ∈ setcmpr y ((y ∈ b) ∧ (y `nin` a)))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∧ (x `nin` b)) ∧ (pars $ (x ∈ b) ∧ (x `nin` a)))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∧ (a `nin` a)) ∧ (pars $ (x ∈ b) ∧ (x `nin` b)))
              , "" & "" =§= setcmpr x (false ∧ false)
              , "" & "" =§= setcmpr x false
              , "" & "" =§= emptyset
            ]


symmetricDifferenceDefinition :: Note
symmetricDifferenceDefinition = de $ do
    let (a, b, x) = ("A", "B", "x")
    s [the, term "symmetric difference", " of two sets ", m a, and, m b, " is the set of all element that are in either ", m a, or, m b, " but not both"]
    ma $ a △ b === setcmpr x ((pars $ (x ∈ a) ∧ (x `nin` b)) ∨ (pars $ (x `nin` a) ∧ (x ∈ b)))

symmetricDifferenceEquivalentDefinition :: Note
symmetricDifferenceEquivalentDefinition = de $ do
    setsDec
    let (a, b, x, y) = ("A", "B", "x", "y")
    ma $ a △ b =§= (pars $ a \\ b) ∪ (pars $ b \\ a)

    proof $ do
        align_ $
            [
              (pars $ a \\ b) ∪ (pars $ b \\ a)
              & "" =§= setcmpr x ((x ∈ a) ∧ (x `nin` b)) ∪ setcmpr x ((x ∈ b) ∧ (x `nin` a))
              , "" & "" =§= setcmpr x ((x ∈ setcmpr y ((y ∈ a) ∧ (y `nin` b))) ∨ (x ∈ setcmpr y ((y ∈ b) ∧ (y `nin` a))))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∧ (x `nin` b)) ∨ (pars $ (x ∈ b) ∧ (x `nin` a)))
              , "" & "" =§= a △ b
            ]

symmetricDifferenceITOUnionAndIntersectionLabel :: Label
symmetricDifferenceITOUnionAndIntersectionLabel = thmlab "sets-symmetric-difference-in-terms-of-union-and-intersection"

symmetricDifferenceITOUnionAndIntersection :: Note
symmetricDifferenceITOUnionAndIntersection = thm $ do
    lab symmetricDifferenceITOUnionAndIntersectionLabel
    setsDec
    let (a, b, x, y) = ("A", "B", "x", "y")
    ma $ a △ b =§= (pars $ a ∪ b) \\ (pars $ a ∩ b)

    proof $ do
        align_ $
          [
            (pars $ a ∪ b) \\ (pars $ a ∩ b)
            & "" =§= setcmpr x ((x ∈ a) ∨ (x ∈ b)) \\ setcmpr x ((x ∈ a) ∧ (x ∈ b))
            , "" & "" =§= setcmpr x (x ∈ setcmpr y ((y ∈ a) ∨ (y ∈ b)) ∧ x `nin` setcmpr y ((y ∈ a) ∧ (y ∈ b)))
            , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∨ (x ∈ b)) ∧ (not . pars $ ((x ∈ a) ∧ (x ∈ b))))
            , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∨ (x ∈ b)) ∧ (pars $ ((x `nin` a) ∨ (x `nin` b))))
            , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∧ (x `nin` b)) ∨ (pars $ (x ∈ b) ∧ (x `nin` a)))
            , "" & "" =§= a △ b
          ]

intersectionOverDifferenceLabel :: Label
intersectionOverDifferenceLabel = thmlab "intersection-over-difference"

intersectionOverDifference :: Note
intersectionOverDifference = thm $ do
    lab intersectionOverDifferenceLabel
    setssDec
    let (a, b, c, x, y) = ("A", "B", "C", "x", "y")
    ma $ a ∩ (pars $ b \\ c) =§= (pars $ a ∩ b) \\ c

    proof $ do
        align_ $
            [
              a ∩ (pars $ b \\ c)
              & "" =§= setcmpr x ((x ∈ a) ∧ x ∈ (b \\ c))
              , "" & "" =§= setcmpr x ((x ∈ a) ∧ x ∈ setcmpr y ((y ∈ b) ∧ (y `nin` c)))
              , "" & "" =§= setcmpr x ((x ∈ a) ∧ (x ∈ b) ∧ (x `nin` c))
              , "" & "" =§= setcmpr x (x ∈ setcmpr y ((y ∈ a) ∧ (y ∈ b)) ∧ (x `nin` c))
              , "" & "" =§= setcmpr x (x ∈ (pars $ a ∩ b) ∧ (x `nin` c))
              , "" & "" =§= (pars $ a ∩ b) \\ c
            ]
