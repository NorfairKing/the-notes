module Functions.Basics (
          functionBasics

        , function          , function_
        , partialFunction   , partialFunction_
        , corange           , corange_
        , codomain          , codomain_

        , total             , total_
        , surjective        , surjective_

        , binaryFunction    , binaryFunction_
    ) where

import           Notes

import           Relations.BasicDefinitions (relation_)
import           Relations.Domain           (domain_, image_)

makeDefs ["function", "partial function", "corange", "codomain", "total", "surjective", "binary function"]

functionBasics :: Notes
functionBasics = notesPart "basics" body

body :: Note
body = do
    section "Basics"

    partialFunctionDefinition
    totalFunctionDefinition
    surjectiveDefinition
    totalFunctionNote
    binaryFunctionDefinition

partialFunctionDefinition :: Note
partialFunctionDefinition = de $ do
    s ["A ", partialFunction', or, function', " ", m funfun, " is a triple ", m funfunc_, " where ", m fundom_, and, funimg_, " are sets and ", m funrel_, " is a single-valued binary ", relation_, " between ", m fundom_, and, m funimg_]
    s ["Each of the sets ", m fundom_, and, funimg_, " have an equivalence relation defined on them, both written as ", m (eqsign)]
    ma $ fa (cs [x, y 1, y 2]) $ (pars $ tuple x (y 1) ∈ funfun ∧ tuple x (y 2) ∈ funfun) ⇒ (y 1 =: y 2)
    s ["The triple ", m funfunc_, " is often written as ", m $ fun funrel_ fundom_ funimg_]
    s [m fundom_, " is called the ", corange', ", ", m funimg_, " is called the ", codomain']
  where
    x = "x"
    y n = "y" !: n

totalFunctionDefinition :: Note
totalFunctionDefinition = de $ do
    s ["A ", function, " ", m funfunc_, " is called ", total', " if its ", corange, " ", m fundom_, " is equal to the ", domain_, " of ", m funrel_]

totalFunctionNote :: Note
totalFunctionNote = nte $ s ["In literature, ", dquoted "function", " often means ", dquoted "total function"]

surjectiveDefinition :: Note
surjectiveDefinition = de $ do
    s ["A ", function, " ", m funfunc_, " is called ", surjective', " if its ", codomain, " ", m funimg_, " is equal to the ", image_, " of ", m funrel_]



binaryFunctionDefinition :: Note
binaryFunctionDefinition = de $ do
    lab binaryFunctionDefinitionLabel
    s ["A ", binaryFunction', " is a function ", m (fun funrel_ fundom_ funimg_), " where ", m fundom_, " is a set of tuples"]

