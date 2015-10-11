module Sets.Algebra.Difference (setDifference, difference) where

import           Notes

difference :: Note
difference = ix "difference"

setDifference :: Notes
setDifference = notesPart "difference" body

body :: Note
body = do
  subsection "Set difference"

  differenceDefinition
  intersectionAndDifferenceDisjunct
  symmetricSetDifferencesDisjunct

  symmetricDifferenceDefinition
  symmetricDifferenceEquivalentDefinition

a, b, x, y :: Note
a = "A"
b = "B"
x = "x"
y = "y"

differenceDefinition :: Note
differenceDefinition = de $ do
  s ["The set ", term "difference", " between sets ", m a, and, m b, " is the set of all elements of ", m a, " that are not in ", m b, "."]
  ma $ a \\ b === setcmpr x ((x ∈ a) &: (x `nin` b))

setsDec :: Note
setsDec = s ["Let ", m a, and, m b, " be sets."]

intersectionAndDifferenceDisjunct :: Note
intersectionAndDifferenceDisjunct = thm $ do
  setsDec
  ma $ ((pars $ a ∩ b) ∩ (pars $ a \\ b)) =§= emptyset

  proof $ do
    align_ $
      [
        ((pars $ a ∩ b) ∩ (pars $ a \\ b))
        & "" =§= (setcmpr x ((x ∈ a) &: (x ∈ b))) ∩ (setcmpr x ((x ∈ a) &: (x `nin` b)))
        , "" & "" =§= setcmpr x (x ∈ (setcmpr y ((y ∈ a) &: (y ∈ b))) &: x ∈ (setcmpr y ((y ∈ a) &: (y `nin` b))))
        , "" & "" =§= setcmpr x ((pars $ (x ∈ a) &: (x ∈ b)) &: (pars $ (x ∈ a) &: (x `nin` b)))
        , "" & "" =§= setcmpr x ((x ∈ a) &: (x ∈ b) &: (x `nin` b))
        , "" & "" =§= setcmpr x ((x ∈ a) &: false)
        , "" & "" =§= setcmpr x false
        , "" & "" =§= emptyset
      ]

symmetricSetDifferencesDisjunct :: Note
symmetricSetDifferencesDisjunct = thm $ do
  setsDec
  ma $ ((pars $ a \\ b) ∩ (pars $ b \\ a)) =§= emptyset

  proof $ do
    align_ $
      [
        ((pars $ a \\ b) ∩ (pars $ b \\ a))
        & "" =§= (setcmpr x ((x ∈ a) &: (x `nin` b))) ∩ (setcmpr x ((x ∈ b) &: (x `nin` a)))
        , "" & "" =§= setcmpr x (x ∈ (setcmpr y ((y ∈ a) &: (y `nin` b))) &: x ∈ (setcmpr y ((y ∈ b) &: (y `nin` a))))
        , "" & "" =§= setcmpr x ((pars $ (x ∈ a) &: (x `nin` b)) &: (pars $ (x ∈ b) &: (x `nin` a)))
        , "" & "" =§= setcmpr x ((pars $ (x ∈ a) &: (a `nin` a)) &: (pars $ (x ∈ b) &: (x `nin` b)))
        , "" & "" =§= setcmpr x (false &: false)
        , "" & "" =§= setcmpr x false
        , "" & "" =§= emptyset
      ]


symmetricDifferenceDefinition :: Note
symmetricDifferenceDefinition = de $ do
  s [the, term "symmetric difference", " of two sets ", m a, and, m b, " is the set of all element that are in either ", m a, or, m b, " but not both."]
  ma $ a △ b === setcmpr x ((pars $ (x ∈ a) &: (x `nin` b)) |: (pars $ (x `nin` a) &: (x ∈ b)))

symmetricDifferenceEquivalentDefinition :: Note
symmetricDifferenceEquivalentDefinition = de $ do
  setsDec
  ma $ a △ b =§= (pars $ a \\ b) ∪ (pars $ b \\ a)

  proof $ do
    align_ $
      [
        (pars $ a \\ b) ∪ (pars $ b \\ a)
        & "" =§= setcmpr x ((x ∈ a) &: (x `nin` b)) ∪ setcmpr x ((x ∈ b) &: (x `nin` a))
        , "" & "" =§= setcmpr x ((x ∈ setcmpr y ((y ∈ a) &: (y `nin` b))) |: (x ∈ setcmpr y ((y ∈ b) &: (y `nin` a))))
        , "" & "" =§= setcmpr x ((pars $ (x ∈ a) &: (x `nin` b)) |: (pars $ (x ∈ b) &: (x `nin` a)))
        , "" & "" =§= a △ b
      ]


