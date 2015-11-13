module Relations.Equivalence (
    equivalenceRelations

  , reflexive
  , symmetric
  , transitive
  ) where

import           Notes

import           Relations.BasicDefinitions (relation)

equivalenceRelations :: Notes
equivalenceRelations = notesPart "equivalence-relations" body

body :: Note
body = do
  section "Equivalence Relations"

  reflexiveDefinition
  symmetricDefinition
  transitiveDefinition
  equivalenceRelationDefinition

reflexive :: Note
reflexive = ix "reflexive"

reflexiveDefinition :: Note
reflexiveDefinition = de $ do
    s ["A ", relation, " ", m rel, " between a set ", m xx, " and itself is called ", term "reflexive", " if it has the following property"]
    ma $ fa (x ∈ xx) (tuple x x ∈ rel)
  where
    x = "x"
    xx = "X"

symmetric :: Note
symmetric = ix "symmetric"

symmetricDefinition :: Note
symmetricDefinition = de $ do
    s ["A ", relation, " ", m rel, " between a set ", m xx, " and itself is called ", term "symmetric", " if it has the following property"]
    ma $ fa (cs [x, y] ∈ xx) (tuple x y ∈ rel ⇔ tuple y x ∈ rel)
  where
    x = "x"
    y = "y"
    xx = "X"

transitive :: Note
transitive = ix "transitive"

transitiveDefinition :: Note
transitiveDefinition = de $ do
    s ["A ", relation, " ", m rel, " between a set ", m xx, " and itself is called ", term "transitive", " if it has the following property"]
    ma $ fa (cs [x, y, z] ∈ xx) $ (pars $ (tuple x y ∈ rel) ∧ (tuple y z ∈ rel)) ⇒ (tuple x z ∈ rel)
  where
    x = "x"
    y = "y"
    z = "z"
    xx = "X"

equivalenceRelationDefinition :: Note
equivalenceRelationDefinition = de $ do
   s ["A ", relation, " ", m rel, " between a set ", m xx, " and itself is called an ", term "equivalence relation", " if it is ", reflexive, ", ", symmetric, and, transitive]
  where xx = "X"




