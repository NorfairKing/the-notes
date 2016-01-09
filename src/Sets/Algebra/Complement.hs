module Sets.Algebra.Complement where

import           Notes

import           Logic.PropositionalLogic.Macro

import           Sets.Algebra.Difference.Terms
import           Sets.Algebra.Intersection.Terms
import           Sets.Algebra.Union.Terms
import           Sets.Basics.Terms

import           Sets.Algebra.Complement.Terms

setComplement :: Note
setComplement = subsection "Set complement" $ do
    complementDefinition
    doubleComplement
    complementaryLawUnion
    complementaryLawIntersection
    firstLawOfDeMorgan
    secondLawOfDeMorgan
    setDifferenceEquivalentDefinition

complementDefinition :: Note
complementDefinition = de $ do
    let (a, b) = ("A", "B")
    s [the, complement', " of a ", set, " ", m a, " relative to a set ", m b, " is the set of all elements of ", m b, " that are not in ", m a]
    ma $ setrelc b a === b \\ a

    s ["When ", m b, " is clear from the context (i.e. there is a universe in play), we just speak about the ", term "complement"]
    ma $ setc a === setrelc setuniv a


doubleComplement :: Note
doubleComplement = thm $ do
    let (a, x, y) = ("A", "x", "y")
    s ["Let ", m a, " be a set"]
    ma $ setc (setc a) =§= a

    proof $ do
        align_ $
            [
              setc (setc a)
              & "" =§= setrelc setuniv (setrelc setuniv a)
            , "" & "" =§= setuniv \\ (pars $ setuniv \\ a)
            , "" & "" =§= setcmpr x ((x ∈ setuniv) ∧ (x `nin` setcmpr y ((y ∈ setuniv) ∧ (y `nin` a))))
            , "" & "" =§= setcmpr x ((x ∈ setuniv) ∧ (not . pars $ (x ∈ setuniv) ∧ (x `nin` a)))
            , "" & "" =§= setcmpr x ((x ∈ setuniv) ∧ (pars $ (x `nin` setuniv) ∨ (x ∈ a)))
            , "" & "" =§= setcmpr x ((pars $ (x ∈ setuniv) ∧ (x `nin` setuniv)) ∨ (pars $ (x ∈ setuniv) ∧ (x ∈ a)))
            , "" & "" =§= setcmpr x ( false ∨ (pars $ true ∧ (x ∈ a)))
            , "" & "" =§= setcmpr x (x ∈ a)
            , "" & "" =§= a
            ]

complementaryLawUnion :: Note
complementaryLawUnion = thm $ do
    lab unionComplementaryLawTheoremLabel
    s [the, term "complementary law", " for the set ", union]
    let (a, b, x, y) = ("A", "B", "x", "y")
    s ["Let ", m a, and, m b, " be sets"]
    ma $ a ∪ setc a =§= setuniv

    proof $ do
        align_ $
            [
                a ∪ setc a
                & "" =§= setcmpr x ((x ∈ a) ∨ (x ∈ setc a))
              , "" & "" =§= setcmpr x ((x ∈ a) ∨ (x ∈ setcmpr y ((y ∈ setuniv) ∧ (y `nin` a))))
              , "" & "" =§= setcmpr x ((x ∈ a) ∨ (pars $ (x ∈ setuniv) ∧ (x `nin` a)))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∨ (x ∈ setuniv)) ∧ (pars $ (x ∈ a) ∨ (x `nin` a)))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∨ true) ∧ true)
              , "" & "" =§= setcmpr x true
              , "" & "" =§= setuniv
            ]

complementaryLawIntersection :: Note
complementaryLawIntersection = thm $ do
    s [the, term "complementary law", " for the set ", intersection]
    let (a, b, x, y) = ("A", "B", "x", "y")
    s ["Let ", m a, and, m b, " be sets"]
    ma $ a ∩ setc a =§= emptyset

    proof $ do
        align_ $
            [
                a ∩ setc a
                & "" =§= setcmpr x ((x ∈ a) ∧ (x ∈ setc a))
              , "" & "" =§= setcmpr x ((x ∈ a) ∧ (x ∈ setcmpr y ((y ∈ setuniv) ∧ (y `nin` a))))
              , "" & "" =§= setcmpr x ((x ∈ a) ∧ (pars $ (x ∈ setuniv) ∧ (x `nin` a)))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∧ (x ∈ setuniv)) ∧ (pars $ (x ∈ a) ∧ (x `nin` a)))
              , "" & "" =§= setcmpr x ((pars $ (x ∈ a) ∧ true) ∧ false)
              , "" & "" =§= setcmpr x false
              , "" & "" =§= emptyset
            ]

firstLawOfDeMorgan :: Note
firstLawOfDeMorgan = thm $ do
    lab firstLawOfDeMorganTheoremLabel
    s [the, term "first law of De Morgan"]

    let (a, b, x, y) = ("A", "B", "x", "y")
    ma $ setc (pars $ a ∪ b) =§= setc a ∩ setc b

    proof $ do
        align_ $
            [
              setc (pars $ a ∪ b)
            & "" =§= setcmpr x (x `nin` (pars $ a ∪ b))
            , "" & "" =§= setcmpr x (x `nin` setcmpr y ((y ∈ a) ∨ (y ∈ b)))
            , "" & "" =§= setcmpr x (not . pars $ ((x ∈ a) ∨ (x ∈ b)))
            , "" & "" =§= setcmpr x ((x `nin` a) ∧ (x `nin` b))
            , "" & "" =§= setcmpr x (x ∈ setcmpr y (y `nin` a) ∧ x ∈ setcmpr y (y `nin` b))
            , "" & "" =§= setcmpr x (x ∈ setc a ∧ x ∈ setc b)
            , "" & "" =§= setc a ∩ setc b
            ]

secondLawOfDeMorgan :: Note
secondLawOfDeMorgan = thm $ do
    lab secondLawOfDeMorganTheoremLabel
    s [the, term "second law of De Morgan"]

    let (a, b, x, y) = ("A", "B", "x", "y")
    ma $ setc (pars $ a ∩ b) =§= setc a ∪ setc b

    proof $ do
        align_ $
            [
              setc (pars $ a ∩ b)
            & "" =§= setcmpr x (x `nin` (pars $ a ∩ b))
            , "" & "" =§= setcmpr x (x `nin` setcmpr y ((y ∈ a) ∧ (y ∈ b)))
            , "" & "" =§= setcmpr x (not . pars $ ((x ∈ a) ∧ (x ∈ b)))
            , "" & "" =§= setcmpr x ((x `nin` a) ∨ (x `nin` b))
            , "" & "" =§= setcmpr x (x ∈ setcmpr y (y `nin` a) ∨ x ∈ setcmpr y (y `nin` b))
            , "" & "" =§= setcmpr x (x ∈ setc a ∨ x ∈ setc b)
            , "" & "" =§= setc a ∪ setc b
            ]


setDifferenceEquivalentDefinition :: Note
setDifferenceEquivalentDefinition = thm $ do
    lab intersectionOverDifferenceTheoremLabel
    let (a, b) = ("A", "B")
    s ["Let ", m a, and, m b, " be sets"]

    ma $ a \\ b =§= a ∩ setc b

    proof $ do
        m $ a \\ b =§= a ∩ (setuniv \\ b) =§= a \\ b
        ref intersectionOverDifferenceTheoremLabel
