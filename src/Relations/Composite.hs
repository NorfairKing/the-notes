module Relations.Composite (compositeRelations) where

import           Notes

import           Macro.Math                 (associative, distributive)
import           Relations.BasicDefinitions (inverseOfInverseIsNormalLabel)

compositeRelations :: Notes
compositeRelations = notesPart "compositeRelations" body

body :: Note
body = do
  section "Composite relations"

  compositeRelationDefinition
  compositeAssociative
  compositeDistributiveWrtInverse

compositeRelationDefinition :: Note
compositeRelationDefinition = de $ do
    s ["Let ", m q, and, m r, " be two binary relations"]
    s ["The composition of ", m q, with, m r, " (read ", dquoted (m q <> " after " <> m r), ") is the following relation"]

    ma $ q ● r === setcmpr (tuple a b) (te c $ (pars $ tuple a c ∈ r) ∧ (pars $ tuple c b ∈ q))

  where
    q = "Q"
    r = "R"
    a = "a"
    b = "b"
    c = "c"

compositeAssociative :: Note
compositeAssociative = thm $ do
    s ["The composition of relations is ", associative]
    s ["Let ", m a, ", ", m b, and, m c, " be binary relations"]

    ma $ (pars $ a ● b) ● c =: a ● (pars $ b ● c)

    proof $ do
      align_
        [
          (pars $ a ● b) ● c
          & "" =: (pars $ setcmpr (tuple x z) (te y $ (pars $ tuple x y ∈ b) ∧ (pars $ tuple y z ∈ a))) ● c
          , "" & "" =: setcmpr (tuple u w) (te v $ (pars $ tuple u v ∈ c) ∧ (pars $ tuple v w ∈ setcmpr (tuple x z) (te y $ (pars $ tuple x y ∈ b) ∧ (pars $ tuple y z ∈ a))))
          , "" & "" =: setcmpr (tuple u z) (te v $ te w $ tuple u v ∈ c ∧ tuple v w ∈ b ∧ tuple w z ∈ a)
          , "" & "" =: setcmpr (tuple u w) (te v $ (pars $ tuple u v ∈ (setcmpr (tuple x z) (te y $ (pars $ tuple x y) ∈ b ∧ (pars $ tuple y z) ∈ a))) ∧ (pars $ tuple v w ∈ a))
          , "" & "" =: setcmpr (tuple u w) (te v $ (pars $ tuple u v ∈ (b ● c)) ∧ (pars $ tuple v w ∈ a))
          , "" & "" =: a ● (pars $ b ● c)
        ]
  where
    a = "A"
    b = "B"
    c = "C"
    u = "u"
    v = "v"
    w = "w"
    x = "x"
    y = "y"
    z = "z"


compositeDistributiveWrtInverse :: Note
compositeDistributiveWrtInverse = thm $ do
    s ["The composition of relations is ", distributive, " with respect to the inverse of relations"]
    s ["Let ", m a, and, m b, " be binary relations"]

    ma $ relinv (pars $ a ● b) =: relinv b ● relinv a

    proof $ do
      align_ $
        [
          relinv (pars $ a ● b)
          & "" =: setcmpr (tuple y x) ((tuple x y) ∈ (a ● b))
          , "" & "" =: setcmpr (tuple y x) ((tuple x y) ∈ (setcmpr (tuple u w) (te v $ (pars $ tuple u v ∈ b) ∧ (pars $ tuple v w ∈ a))))
          , "" & "" =: setcmpr (tuple w u) (te v $ (pars $ tuple u v ∈ b) ∧ (pars $ tuple v w ∈ a))
          , "" & "" =: setcmpr (tuple w u) (te v $ (pars $ tuple u v ∈ (setcmpr (tuple u v) (tuple v u ∈ relinv b))) ∧ (pars $ tuple v w ∈ (setcmpr (tuple v w) (tuple w v ∈ relinv a))))
          , "" & "" =: setcmpr (tuple w u) (te v $ (pars $ tuple v u ∈ relinv b) ∧ (pars $ tuple w v ∈ relinv a))
          , "" & "" =: relinv b ● relinv a
        ]
      s ["Note that we use that the inverse of the inverse of a relation is the original relation", ref inverseOfInverseIsNormalLabel]

  where
    a = "A"
    b = "B"
    u = "u"
    v = "v"
    w = "w"
    x = "x"
    y = "y"

-- TODO distributivity with inverse
-- TODO domain after composition
-- TODO image after composition
-- TODO if the image of the second is a part of the domain of the first, then the domain of the composition is the domain of the second. really? sure? make sure to prove it!
