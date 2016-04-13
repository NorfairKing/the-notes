module Functions.Basics where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Relations.Basics.Terms         hiding (total, total')
import           Relations.Domain.Terms
import           Sets.Basics.Terms

import           Functions.Jections.Terms

import           Functions.Basics.Macro
import           Functions.Basics.Terms

basics :: Note
basics = section "Basics" $ do
    partialFunctionDefinition
    totalFunctionDefinition
    surjectiveDefinition
    totalFunctionNote
    binaryFunctionDefinition
    ternaryFunctionDefinition

    predicateEquivalentDefinition
    unitFunctionDefinition


partialFunctionDefinition :: Note
partialFunctionDefinition = de $ do
    lab functionDefinitionLabel
    lab partialFunctionDefinitionLabel
    s ["A ", partialFunction', or, function', " ", m fun_, " is a triple ", m t , " where ", m dom_, and, img_, " are sets and ", m fun_, " is a single-valued binary ", relation_, " between ", m dom_, and, m img_]
    ma $ fa (cs [x, y 1, y 2]) $ (pars $ tuple x (y 1) ∈ fun_ ∧ tuple x (y 2) ∈ fun_) ⇒ (y 1 =: y 2)
    s ["The triple ", m t, " is often written as ", m $ fun fun_ dom_ img_]
    s [m dom_, " is called the ", corange', ", ", m img_, " is called the ", codomain']
  where
    x = "x"
    y n = "y" !: n
    t = (triple fun_ dom_ img_)

totalFunctionDefinition :: Note
totalFunctionDefinition = de $ do
    s ["A ", function, " ", m funfunc_, " is called ", total', " if its ", corange, " ", m dom_, " is equal to the ", domain_, " of ", m fun_]

totalFunctionNote :: Note
totalFunctionNote = nte $ s ["In mathematical literature, ", dquoted "function", " often means ", dquoted "total function"]

surjectiveDefinition :: Note
surjectiveDefinition = de $ do
    s ["A ", function, " ", m funfunc_, " is called ", surjective', " if its ", codomain, " ", m img_, " is equal to the ", image_, " of ", m fun_]



binaryFunctionDefinition :: Note
binaryFunctionDefinition = de $ do
    lab binaryFunctionDefinitionLabel
    s ["A ", binaryFunction', " is a function ", m (fun fun_ dom_ img_), " where ", m dom_, " is a set of tuples"]


ternaryFunctionDefinition :: Note
ternaryFunctionDefinition = de $ do
    lab ternaryFunctionDefinitionLabel
    s ["A ", ternaryFunction', " is a function ", m (fun fun_ dom_ img_), " where ", m dom_, " is a set of triples"]

predicateEquivalentDefinition :: Note
predicateEquivalentDefinition = thm $ do
    let p_ = "P"
        a = "A"
    s ["A", predicate_, m p_, "on a", set, m a, "can equivalently be defined as a", function, m $ fun p_ a (setofs [false, true]), "that deides whether the", predicate, "holds for an", element]

    toprove


unitFunctionDefinition :: Note
unitFunctionDefinition = do
    de $ do
        lab unitFunctionDefinitionLabel
        let a = "A"
            e = comm0 "bullet"
        s ["For a given", domain, m a, "the", unitFunction', "is the", total, function, "that maps every", element, "of", m a, "to a", quoted "dummy", element, m e]
        let x = "x"
        ma $ unitf a =: setcmpr (tuple x e) (x ∈ a)
    nte $ do
        s ["This dummy", element, "just signifies that all information is lost in this", unitFunction]








