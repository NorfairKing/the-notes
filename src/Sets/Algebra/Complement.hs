module Sets.Algebra.Complement (
    setComplement
  , complement

  , unionComplementaryLawLabel
  , firstLawOfDeMorganLabel
  , secondLawOfDeMorganLabel
  ) where

import           Notes

import           Sets.Algebra.Intersection (intersection)
import           Sets.Algebra.Union        (union)

complement :: Note
complement = ix "complement"

setComplement :: Notes
setComplement = notesPart "complement" body

body :: Note
body = do
  subsection "Set complement"
  complementDefinition
  doubleComplement
  complementaryLawUnion
  complementaryLawIntersection
  firstLawOfDeMorgan
  secondLawOfDeMorgan

a, b, x, y :: Note
a = "A"
b = "B"
c = "C"
x = "x"
y = "y"

setsDec :: Note
setsDec = s ["Let ", m a, and, m b, " be sets."]

complementDefinition :: Note
complementDefinition = de $ do
  s [the, term "complement", " of a set ", m a, " relative to a set ", m b, " is the set of all elements of ", m b, " that are not in ", m a, "."]
  ma $ setrelc b a === b \\ a

  s ["When ", m b, " is clear from the context (i.e. there is a universe in play), we just speak about the ", term "complement", ":"]
  ma $ setc a === setrelc setuniv a


doubleComplement :: Note
doubleComplement = thm $ do
  s ["Let ", m a, " be a set."]
  ma $ setc (setc a) =§= a

  proof $ do
    align_ $
      [
        setc (setc a)
        & "" =§= setrelc setuniv (setrelc setuniv a)
      , "" & "" =§= setuniv \\ (pars $ setuniv \\ a)
      , "" & "" =§= setcmpr x ((x ∈ setuniv) &: (x `nin` setcmpr y ((y ∈ setuniv) &: (y `nin` a))))
      , "" & "" =§= setcmpr x ((x ∈ setuniv) &: (not . pars $ (x ∈ setuniv) &: (x `nin` a)))
      , "" & "" =§= setcmpr x ((x ∈ setuniv) &: (pars $ (x `nin` setuniv) |: (x ∈ a)))
      , "" & "" =§= setcmpr x ((pars $ (x ∈ setuniv) &: (x `nin` setuniv)) |: (pars $ (x ∈ setuniv) &: (x ∈ a)))
      , "" & "" =§= setcmpr x ( false |: (pars $ true &: (x ∈ a)))
      , "" & "" =§= setcmpr x (x ∈ a)
      , "" & "" =§= a
      ]

unionComplementaryLawLabel :: Label
unionComplementaryLawLabel = thmlab "complementary-law-union"

complementaryLawUnion :: Note
complementaryLawUnion = thm $ do
  lab unionComplementaryLawLabel
  s [the, term "complementary law", " for the set ", union, "."]
  setsDec
  ma $ a ∪ (setc a) =§= setuniv

  proof $ do
    align_ $
      [
          a ∪ (setc a)
          & "" =§= setcmpr x ((x ∈ a) |: (x ∈ setc a))
        , "" & "" =§= setcmpr x ((x ∈ a) |: (x ∈ setcmpr y ((y ∈ setuniv) &: (y `nin` a))))
        , "" & "" =§= setcmpr x ((x ∈ a) |: (pars $ (x ∈ setuniv) &: (x `nin` a)))
        , "" & "" =§= setcmpr x ((pars $ (x ∈ a) |: (x ∈ setuniv)) &: (pars $ (x ∈ a) |: (x `nin` a)))
        , "" & "" =§= setcmpr x ((pars $ (x ∈ a) |: true) &: true)
        , "" & "" =§= setcmpr x true
        , "" & "" =§= setuniv
      ]

complementaryLawIntersection :: Note
complementaryLawIntersection = thm $ do
  s [the, term "complementary law", " for the set ", intersection, "."]
  setsDec
  ma $ a ∩ (setc a) =§= emptyset

  proof $ do
    align_ $
      [
          a ∩ (setc a)
          & "" =§= setcmpr x ((x ∈ a) &: (x ∈ setc a))
        , "" & "" =§= setcmpr x ((x ∈ a) &: (x ∈ setcmpr y ((y ∈ setuniv) &: (y `nin` a))))
        , "" & "" =§= setcmpr x ((x ∈ a) &: (pars $ (x ∈ setuniv) &: (x `nin` a)))
        , "" & "" =§= setcmpr x ((pars $ (x ∈ a) &: (x ∈ setuniv)) &: (pars $ (x ∈ a) &: (x `nin` a)))
        , "" & "" =§= setcmpr x ((pars $ (x ∈ a) &: true) &: false)
        , "" & "" =§= setcmpr x false
        , "" & "" =§= emptyset
      ]

firstLawOfDeMorganLabel :: Label
firstLawOfDeMorganLabel = thmlab "first-law-of-de-morgan"

firstLawOfDeMorgan :: Note
firstLawOfDeMorgan = thm $ do
  lab firstLawOfDeMorganLabel
  s [the, term "first law of De Morgan", "."]

  ma $ setc (pars $ a ∪ b) =§= setc a ∩ setc b

  proof $ do
    align_ $
      [
        setc (pars $ a ∪ b)
      & "" =§= setcmpr x (x `nin` (pars $ a ∪ b))
      , "" & "" =§= setcmpr x (x `nin` (setcmpr y ((y ∈ a) |: (y ∈ b))))
      , "" & "" =§= setcmpr x (not . pars $ ((x ∈ a) |: (x ∈ b)))
      , "" & "" =§= setcmpr x ((x `nin` a) &: (x `nin` b))
      , "" & "" =§= setcmpr x (x ∈ setcmpr y (y `nin` a) &: x ∈ setcmpr y (y `nin` b))
      , "" & "" =§= setcmpr x (x ∈ setc a &: x ∈ setc b)
      , "" & "" =§= setc a ∩ setc b
      ]

secondLawOfDeMorganLabel :: Label
secondLawOfDeMorganLabel = thmlab "second-law-of-de-morgan"

secondLawOfDeMorgan :: Note
secondLawOfDeMorgan = thm $ do
  lab secondLawOfDeMorganLabel
  s [the, term "second law of De Morgan", "."]

  ma $ setc (pars $ a ∩ b) =§= setc a ∪ setc b

  proof $ do
    align_ $
      [
        setc (pars $ a ∩ b)
      & "" =§= setcmpr x (x `nin` (pars $ a ∩ b))
      , "" & "" =§= setcmpr x (x `nin` (setcmpr y ((y ∈ a) &: (y ∈ b))))
      , "" & "" =§= setcmpr x (not . pars $ ((x ∈ a) &: (x ∈ b)))
      , "" & "" =§= setcmpr x ((x `nin` a) |: (x `nin` b))
      , "" & "" =§= setcmpr x (x ∈ setcmpr y (y `nin` a) |: x ∈ setcmpr y (y `nin` b))
      , "" & "" =§= setcmpr x (x ∈ setc a |: x ∈ setc b)
      , "" & "" =§= setc a ∪ setc b
      ]
