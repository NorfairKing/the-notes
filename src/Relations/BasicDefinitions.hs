module Relations.BasicDefinitions (
    basicDefinitions

  , relation    , relation_     , relationDefinitionLabel
  , inverseOfInverseIsNormalLabel

  , reflexive   , reflexive_    , reflexiveDefinitionLabel
  , symmetric   , symmetric_    , symmetricDefinitionLabel
  , transitive  , transitive_   , transitiveDefinitionLabel
  , total       , total_        , totalDefinitionLabel
  ) where

import           Notes

import           Sets.CarthesianProduct (carthesianProduct_)

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


relation :: Note
relation = ix "relation"

relation_ :: Note
relation_ = relation <> ref relationDefinitionLabel

relationDefinitionLabel :: Label
relationDefinitionLabel = Label Definition "relation"

relationDefinition :: Note
relationDefinition = de $ do
    lab relationDefinitionLabel
    s ["A ", term "relation", " between ", m n, " sets ", m $ cs [x 1, x 2, dotsc, x n], " is a subset of their ", carthesianProduct_]
  where
    n = "n"
    x i = "X" !: i

binaryRelationDefinition :: Note
binaryRelationDefinition = de $ do
  s ["A binary ", relation, " " , m rel, " is a relation between two sets"]
  s ["If a binary relation ", m rel, " between sets ", m a, and, m b, " contains a tuple ", m $ tuple v w, " then that is often denoted as ", m $ inrel v w]
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
    s ["The ", m n, "-ary ", term "unit relation", " ", m (relunit_ n), " is the set of all tuples of the same element"]
    ma $ relunit_ 2 === setcmpr (tuple v v) (v ∈ x)
    ma $ relunit_ n === setcmpr (pars $ list v v v) (v ∈ x)
  where
    x = "X"
    v = "v"
    n = "n"

inverseRelationDefinition :: Note
inverseRelationDefinition = de $ do
    s ["Let ", m rel, " be a binary relation on the sets ", m a, and, m b]
    s [the, term "inverse relation", " ", m (relinv rel), " of ", m rel, " is the following relation"]
    ma $ relinv rel === setcmpr (tuple y x) (tuple x y ∈ rel)
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
    s ["Let ", m rel, " be a binary relation on the sets ", m a, and, m b]
    ma $ relinv (relinv rel) =: rel

    proof $ do
      align_
        [
          relinv (relinv rel)
          & "" =: setcmpr (tuple y x) (tuple x y ∈ (relinv rel))
          , "" & "" =: setcmpr (tuple y x) (tuple x y ∈ (setcmpr (tuple y x) (tuple x y ∈ rel)))
          , "" & "" =: setcmpr (tuple y x) (tuple y x ∈ rel)
          & "" =: rel
        ]
  where
    a = "A"
    b = "B"
    x = "x"
    y = "y"

reflexive :: Note
reflexive = ix "reflexive"

reflexive_ :: Note
reflexive_ = reflexive <> ref reflexiveDefinitionLabel

reflexiveDefinitionLabel :: Label
reflexiveDefinitionLabel = Label Definition "reflexive"

reflexiveDefinition :: Note
reflexiveDefinition = de $ do
    lab reflexiveDefinitionLabel
    s ["A ", relation, " ", m rel, " between a set ", m xx, " and itself is called ", term "reflexive", " if it has the following property"]
    ma $ fa (x ∈ xx) (tuple x x ∈ rel)
  where
    x = "x"
    xx = "X"

transitive :: Note
transitive = ix "transitive"

transitive_ :: Note
transitive_ = transitive <> ref transitiveDefinitionLabel

transitiveDefinitionLabel :: Label
transitiveDefinitionLabel = Label Definition "transitive"

transitiveDefinition :: Note
transitiveDefinition = de $ do
    lab transitiveDefinitionLabel
    s ["A ", relation, " ", m rel, " between a set ", m xx, " and itself is called ", term "transitive", " if it has the following property"]
    ma $ fa (cs [x, y, z] ∈ xx) $ (pars $ (tuple x y ∈ rel) ∧ (tuple y z ∈ rel)) ⇒ (tuple x z ∈ rel)
  where
    x = "x"
    y = "y"
    z = "z"
    xx = "X"

symmetric :: Note
symmetric = ix "symmetric"

symmetric_ :: Note
symmetric_ = symmetric <> ref symmetricDefinitionLabel

symmetricDefinitionLabel :: Label
symmetricDefinitionLabel = Label Definition "symmetric"

symmetricDefinition :: Note
symmetricDefinition = de $ do
    lab symmetricDefinitionLabel
    s ["A ", relation, " ", m rel, " between a set ", m xx, " and itself is called ", term "symmetric", " if it has the following property"]
    ma $ fa (cs [x, y] ∈ xx) (tuple x y ∈ rel ⇔ tuple y x ∈ rel)
  where
    x = "x"
    y = "y"
    xx = "X"



total :: Note
total = ix "total"

total_ :: Note
total_ = total <> ref totalDefinitionLabel

totalDefinitionLabel :: Label
totalDefinitionLabel = Label Definition "total-relation"

totalDefinition :: Note
totalDefinition = de $ do
    lab totalDefinitionLabel
    s ["A binary ", relation, " ", m rel, " is called ", term "total", " if it has the following property"]
    ma $ fa (cs [x, y]) ((x `inrel` y) ∨ (y `inrel` x))
  where
    x = "x"
    y = "y"

totalityImpliesReflexivity :: Note
totalityImpliesReflexivity = thm $ do
    s ["Every total relation is reflexive"]

    proof $ do
      s ["Let ", m rel, " be a total relation on a set ", m xx, " and ", m x, " an element of ", m xx]
      s ["Because ", m rel, " is total, either ", m (x `inrel` x), or, m (x `inrel` x), " must be true"]
      s ["This means that ", m (x `inrel` x), " must hold and ", m rel, " must therefore be reflexive"]
    toprove

  where
    x = "x"
    xx = "X"
