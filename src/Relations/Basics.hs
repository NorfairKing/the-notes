module Relations.Basics where
import           Notes

import           Sets.CarthesianProduct (carthesianProduct_)

import           Relations.Basics.Macro

makeDefs [
      "relation"
    , "unit relation"
    , "inverse relation"

    , "reflexive"
    , "transitive"
    , "symmetric"
    , "total"
    ]

basicDefinitions :: Notes
basicDefinitions = notesPart "definitions" $ do
  section "Basics"

  relationDefinition
  binaryRelationDefinition
  ternaryRelationDefinition
  unitRelationDefinition
  inverseRelationDefinition

  inverseOfInverseIsNormal

  subsection "Properties of relations"

  reflexiveDefinition
  transitiveDefinition
  symmetricDefinition
  totalDefinition

  totalityImpliesReflexivity


relationDefinition :: Note
relationDefinition = de $ do
    lab relationDefinitionLabel
    s ["A ", relation', " between ", m n, " sets ", m $ cs [x 1, x 2, dotsc, x n], " is a subset of their ", carthesianProduct_]
  where
    n = "n"
    x i = "X" !: i

binaryRelationDefinition :: Note
binaryRelationDefinition = de $ do
  s ["A binary ", relation, " " , m rel_, " is a relation between two sets"]
  s ["If a binary relation ", m rel_, " between sets ", m a, and, m b, " contains a tuple ", m $ tuple v w, " then that is often denoted as ", m $ elem_ v w]
  where
    a = "A"
    b = "B"
    v = "v"
    w = "w"

ternaryRelationDefinition :: Note
ternaryRelationDefinition = de $ s ["A ternary ", relation, " is a relation between three sets"]

unitRelationDefinition :: Note
unitRelationDefinition = de $ do
    s ["Let ", m x, " be a set"]
    s ["The ", m n, "-ary ", unitRelation', " ", m (unit n), " is the set of all tuples of the same element"]
    ma $ unit 2 === setcmpr (tuple v v) (v ∈ x)
    ma $ unit n === setcmpr (pars $ list v v v) (v ∈ x)
  where
    x = "X"
    v = "v"
    n = "n"

inverseRelationDefinition :: Note
inverseRelationDefinition = de $ do
    s ["Let ", m rel_, " be a binary relation on the sets ", m a, and, m b]
    s [the, inverseRelation', " ", m (inv rel_), " of ", m rel_, " is the following relation"]
    ma $ inv rel_ === setcmpr (tuple y x) (tuple x y ∈ rel_)
  where
    a = "A"
    b = "B"
    x = "x"
    y = "y"

inverseOfInverseIsNormalLabel :: Label
inverseOfInverseIsNormalLabel = Label Theorem "inverse-of-inverse-relation-is-normal"

inverseOfInverseIsNormal :: Note
inverseOfInverseIsNormal = thm $ do
    lab inverseOfInverseIsNormalLabel
    s ["Let ", m rel_, " be a binary relation on the sets ", m a, and, m b]
    ma $ inv (inv rel_) =: rel_

    proof $ do
      align_
        [
          inv (inv rel_)
          & "" =: setcmpr (tuple y x) (tuple x y ∈ (inv rel_))
          , "" & "" =: setcmpr (tuple y x) (tuple x y ∈ (setcmpr (tuple y x) (tuple x y ∈ rel_)))
          , "" & "" =: setcmpr (tuple y x) (tuple y x ∈ rel_)
          & "" =: rel_
        ]
  where
    a = "A"
    b = "B"
    x = "x"
    y = "y"

reflexiveDefinition :: Note
reflexiveDefinition = de $ do
    lab reflexiveDefinitionLabel
    s ["A ", relation, " ", m rel_, " between a set ", m xx, " and itself is called ", reflexive', " if it has the following property"]
    ma $ fa (x ∈ xx) (tuple x x ∈ rel_)
  where
    x = "x"
    xx = "X"

transitiveDefinition :: Note
transitiveDefinition = de $ do
    lab transitiveDefinitionLabel
    s ["A ", relation, " ", m rel_, " between a set ", m xx, " and itself is called ", transitive', " if it has the following property"]
    ma $ fa (cs [x, y, z] ∈ xx) $ (pars $ (tuple x y ∈ rel_) ∧ (tuple y z ∈ rel_)) ⇒ (tuple x z ∈ rel_)
  where
    x = "x"
    y = "y"
    z = "z"
    xx = "X"

symmetricDefinition :: Note
symmetricDefinition = de $ do
    lab symmetricDefinitionLabel
    s ["A ", relation, " ", m rel_, " between a set ", m xx, " and itself is called ", symmetric', " if it has the following property"]
    ma $ fa (cs [x, y] ∈ xx) (tuple x y ∈ rel_ ⇔ tuple y x ∈ rel_)
  where
    x = "x"
    y = "y"
    xx = "X"

totalDefinition :: Note
totalDefinition = de $ do
    lab totalDefinitionLabel
    s ["A binary ", relation, " ", m rel_, " is called ", total', " if it has the following property"]
    ma $ fa (cs [x, y]) ((x `elem_` y) ∨ (y `elem_` x))
  where
    x = "x"
    y = "y"

totalityImpliesReflexivity :: Note
totalityImpliesReflexivity = thm $ do
    s ["Every total relation is reflexive"]

    proof $ do
      s ["Let ", m rel_, " be a total relation on a set ", m xx, " and ", m x, " an element of ", m xx]
      s ["Because ", m rel_, " is total, either ", m (x `elem_` x), or, m (x `elem_` x), " must be true"]
      s ["This means that ", m (x `elem_` x), " must hold and ", m rel_, " must therefore be reflexive"]
    toprove

  where
    x = "x"
    xx = "X"
