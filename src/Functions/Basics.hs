module Functions.Basics where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Relations.Basics               (relation_)
import           Relations.Domain               (domain_, image_)
import           Sets.Basics.Terms


import           Functions.Application.Macro
import           Functions.Basics.Macro

makeDefs [
      "function"
    , "partial function"
    , "corange"
    , "codomain"
    , "total"
    , "surjective"
    , "binary function"
    , "ternary function"
    , "member-wise application"
    ]

basics :: Note
basics = note "basics" $ do
    section "Basics"

    partialFunctionDefinition
    totalFunctionDefinition
    surjectiveDefinition
    totalFunctionNote
    binaryFunctionDefinition
    ternaryFunctionDefinition

    memberwiseApplication


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

memberwiseApplication :: Note
memberwiseApplication = de $ do
    s ["Let ", m funfunc_, " be a ", function]
    s [the, memberWiseApplication', " of ", m funfunc_, " to a ", subset, " ", m ss, " of ", m dom_, " is the set of all applications of ", m fun_, " to members of ", m ss, " and is denoted as ", m (fun_ `mwfn` ss)]
    ma $ fun_ `mwfn` ss === setcmpr (fun_ `fn` e) (e ∈ ss)
  where
    ss = "S"
    e = "s"
