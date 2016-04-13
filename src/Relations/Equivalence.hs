module Relations.Equivalence where

import           Notes

import           Logic.PropositionalLogic.Macro

import           Relations.Basics.Terms
import           Relations.Preorders.Macro
import           Relations.Preorders.Terms

import           Relations.Equivalence.Macro
import           Relations.Equivalence.Terms

equivalenceRelationS :: Note
equivalenceRelationS = section "Equivalence Relations" $ do
    equivalenceRelationDefinition
    equivalenceClassesSS

equivalenceRelationDefinition :: Note
equivalenceRelationDefinition = de $ do
    lab equivalenceRelationDefinitionLabel
    s ["A ", symmetric_, " ", preorder, " is called an ", equivalenceRelation']

equivalenceClassesSS :: Note
equivalenceClassesSS = subsection "Equivalence Classes" $ do
    equivalenceClassDefinition

    totheorem "The equivalence class of an element contains that element"
    totheorem "If two elements are equivalent, then their equivalence classes are equal"

    inducedEquivalenceRelation

    quotientSetDefinition
    totheorem "The quotient set is a partition"
    totheorem "A partition induces an equivalence relation"


equivalenceClassDefinition :: Note
equivalenceClassDefinition = de $ do
    s ["Let ", m eqrel_, " be an ", equivalenceRelation, " on a set ", m xx, " and let ", m x, " be an element of ", m xx]
    s ["The ", equivalenceClass', " ", m (eqcl_ x), " of ", m x, " in ", m eqrel_, " is the set of all elements that are equivalent to ", m x]

    ma $ eqcl_ x === setcmpr (y ∈ xx) (x .~ y)
  where
    x = "x"
    y = "y"
    xx = "X"

quotientSetDefinition :: Note
quotientSetDefinition = de $ do
    lab quotientSetDefinitionLabel
    s ["Let ", m eqrel_, " be an ", equivalenceRelation, " on a set ", m xx]
    s ["The ", quotientSet', " ", m (eqrel_ `eqcls` xx),  " of ", m xx, " with respect to ", m eqrel_, " is the set of all equivalennce classes of ", m xx, " in ", m eqrel_]

    ma $ (xx ./~ eqrel_) === setcmpr (eqcl_ x) (x ∈ xx)
  where
    x = "x"
    xx = "X"

inducedEquivalenceRelation :: Note
inducedEquivalenceRelation = thm $ do
    s ["Let ", m preord_, " be a preord_er on a set ", m xx]
    s ["The relation ", m indeqrel, " is an equivalence relation"]

    ma $ indeqrel === (setcmpr (tuple a b) $ inpreord_ a b ∧ inpreord_ b a)

    toprove
  where
    indeqrel = eqrel_ !: preord_
    a = "a"
    b = "b"
    xx = "X"








