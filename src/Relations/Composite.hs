module Relations.Composite (compositeRelations) where

import           Notes

import           Functions.BinaryOperation (associative_)
import           Relations.Basics          (inverseOfInverseIsNormalLabel)

import           Relations.Basics.Macro
import           Relations.Composite.Macro
import           Relations.Domain.Macro

compositeRelations :: Note
compositeRelations = note "composite-relations" body

body :: Note
body = do
    subsection "Composite relations"

    compositeRelationDefinition
    compositeAssociative
    compositeDistributiveWrtInverse

    domainAfterComposition
    imageAfterComposition


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
    s ["The composition of relations is ", associative_]
    s ["Let ", m a, ", ", m b, and, m c, " be binary relations"]

    ma $ (pars $ a ● b) ● c =: a ● (pars $ b ● c)

    proof $ do
      align_
        [
          (pars $ a ● b) ● c
          & "" =: (pars $ setcmpr (tuple x z) (te y $ (pars $ tuple x y ∈ b) ∧ (pars $ tuple y z ∈ a))) ● c
          , "" & "" =: setcmpr (tuple u w) (te v $ (pars $ tuple u v ∈ c) ∧ (pars $ tuple v w ∈ setcmpr (tuple x z) (te y $ (pars $ tuple x y ∈ b) ∧ (pars $ tuple y z ∈ a))))
          , "" & "" =: setcmpr (tuple u z) (te v $ te w $ tuple u v ∈ c ∧ tuple v w ∈ b ∧ tuple w z ∈ a)
          , "" & "" =: setcmpr (tuple u w) (te v $ (pars $ tuple u v ∈ setcmpr (tuple x z) (te y $ (pars $ tuple x y) ∈ b ∧ (pars $ tuple y z) ∈ a)) ∧ (pars $ tuple v w ∈ a))
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

    ma $ inv (pars $ a ● b) =: inv b ● inv a

    proof $ do
      align_ $
        [
          inv (pars $ a ● b)
          & "" =: setcmpr (tuple y x) (tuple x y ∈ (a ● b))
          , "" & "" =: setcmpr (tuple y x) (tuple x y ∈ setcmpr (tuple u w) (te v $ (pars $ tuple u v ∈ b) ∧ (pars $ tuple v w ∈ a)))
          , "" & "" =: setcmpr (tuple w u) (te v $ (pars $ tuple u v ∈ b) ∧ (pars $ tuple v w ∈ a))
          , "" & "" =: setcmpr (tuple w u) (te v $ (pars $ tuple u v ∈ setcmpr (tuple u v) (tuple v u ∈ inv b)) ∧ (pars $ tuple v w ∈ setcmpr (tuple v w) (tuple w v ∈ inv a)))
          , "" & "" =: setcmpr (tuple w u) (te v $ (pars $ tuple v u ∈ inv b) ∧ (pars $ tuple w v ∈ inv a))
          , "" & "" =: inv b ● inv a
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


domainAfterComposition :: Note
domainAfterComposition = thm $ do
    s ["Let ", m a, and, m b, " be relations"]
    ma $ dom (b ● a) ⊆ dom a

    proof $ align_
      [
        dom (b ● a)
        & "" =: setcmpr x (te y $ tuple x y ∈ b ● a)
        , "" & "" =: setcmpr x (te y $ tuple x y ∈ setcmpr (tuple u w) (te v $ (pars $ tuple u v ∈ b) ∧ (pars $ tuple v w ∈ a)))
        , "" & "" =: setcmpr x (te v $ te w $ (pars $ tuple u v ∈ b) ∧ (pars $ tuple v w ∈ a))
        , "" & "" ⊆ setcmpr x (te w $ tuple v w ∈ a)
        , "" & "" =: dom a
      ]
  where
    a = "A"
    b = "B"
    u = "u"
    v = "v"
    w = "w"
    x = "x"
    y = "y"


imageAfterComposition :: Note
imageAfterComposition = thm $ do
    s ["Let ", m a, and, m b, " be relations"]
    ma $ img (b ● a) ⊆ img b

    proof $ align_
      [
        img (b ● a)
        & "" =: setcmpr y (te x $ tuple x y ∈ b ● a)
        , "" & "" =: setcmpr y (te x $ tuple x y ∈ setcmpr (tuple u w) (te v $ (pars $ tuple u v ∈ b) ∧ (pars $ tuple v w ∈ a)))
        , "" & "" =: setcmpr y (te v $ te u $ (pars $ tuple u v ∈ b) ∧ (pars $ tuple v w ∈ a))
        , "" & "" ⊆ setcmpr y (te u $ tuple u v ∈ b)
        , "" & "" =: img b
      ]
  where
    a = "A"
    b = "B"
    u = "u"
    v = "v"
    w = "w"
    x = "x"
    y = "y"

-- TODO if the image of the first is a part of the domain of the second, then the domain of the composition is the domain of the second. really? sure? make sure to prove it!
