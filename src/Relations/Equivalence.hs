module Relations.Equivalence where

import           Notes

import           Relations.BasicDefinitions (reflexive_, relation, symmetric_,
                                             transitive_)

makeDefs [
      "preorder"
    , "equivalence relation"
    ]

equivalenceRelations :: Notes
equivalenceRelations = notesPart "equivalence-relations" body

body :: Note
body = do
  section "Equivalence Relations"

  basicDefinitions
  equivalenceClasses

basicDefinitions :: Note
basicDefinitions = do
  preorderDefinition
  equivalenceRelationDefinition

preorderDefinition :: Note
preorderDefinition = de $ do
    lab preorderDefinitionLabel
    s ["A ", relation, " ", m rel, " between a set ", m xx, " and itself is called an ", preorder', " if it is ", reflexive_, and, transitive_]
  where xx = "X"

equivalenceRelationDefinition :: Note
equivalenceRelationDefinition = de $ do
    lab equivalenceRelationDefinitionLabel
    s ["A ", symmetric_, " ", preorder, " is called an ", equivalenceRelation']

equivalenceClasses :: Note
equivalenceClasses = do
  subsection "Equivalence Classes"

  equivalenceClassDefinition

  totheorem "The equivalence class of an element contains that element"
  totheorem "If two elements are equivalent, then their equivalence classes are equal"

  inducedEquivalenceRelation

  quotientSetDefinition
  totheorem "The quotient set is a partition"
  totheorem "A partition induces an equivalence relation"


equivalenceClass :: Note
equivalenceClass = ix "equivalence class"

equivalenceClassDefinition :: Note
equivalenceClassDefinition = de $ do
    s ["Let ", m eqrel, " be an ", equivalenceRelation, " on a set ", m xx, " and let ", m x, " be an element of ", m xx]
    s ["The ", term "equivalence class", " ", m (eqcl_ eqrel x), " of ", m x, " in ", m eqrel, " is the set of all elements that are equivalent to ", m x]

    ma $ eqcl_ eqrel x === setcmpr (y ∈ xx) (x .~ y)
  where
    x = "x"
    y = "y"
    xx = "X"

quotientSetDefinition :: Note
quotientSetDefinition = de $ do
    s ["Let ", m eqrel, " be an ", equivalenceRelation, " on a set ", m xx]
    s ["The ", term "quotient set", " ", m (eqrel `eqcls` xx),  " of ", m xx, " with respect to ", m eqrel, " is the set of all equivalennce classes of ", m xx, " in ", m eqrel]

    ma $ (eqrel `eqcls` xx) === setcmpr (eqcl_ eqrel x) (x ∈ xx)
  where
    x = "x"
    xx = "X"

inducedEquivalenceRelation :: Note
inducedEquivalenceRelation = thm $ do
    s ["Let ", m preord, " be a preorder on a set ", m xx]
    s ["The relation ", m indeqrel, " is an equivalence relation"]

    ma $ indeqrel === (setcmpr (tuple a b) $ inpreord a b ∧ inpreord b a)

    toprove
  where
    indeqrel = eqrel !: preord
    a = "a"
    b = "b"
    xx = "X"








