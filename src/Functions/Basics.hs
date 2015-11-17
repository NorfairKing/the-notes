module Functions.Basics (
          functionBasics

        , function
        , partialFunction
        , corange
        , codomain

        , total
        , surjective
    ) where

import           Notes

import           Relations.BasicDefinitions (relation_)
import           Relations.Domain           (domain_, image_)

functionBasics :: Notes
functionBasics = notesPart "basics" body

body :: Note
body = do
    section "Basics"

    partialFunctionDefinition
    totalFunctionDefinition
    surjectiveDefinition
    totalFunctionNote

function :: Note
function = ix "function"

partialFunction :: Note
partialFunction = ix "partial function"

corange :: Note
corange = ix "corange"

codomain :: Note
codomain = ix "codomain"

partialFunctionDefinition :: Note
partialFunctionDefinition = de $ do
    s ["A (partial) ", term "function", " ", m funfun, " is a triple ", m funfunc_, " where ", m fundom_, and, funimg_, " are sets and ", m funrel_, " is a single-valued binary ", relation_, " between ", m fundom_, and, m funimg_]
    ma $ fa (cs [x, y 1, y 2]) $ (pars $ tuple x (y 1) ∈ funfun ∧ tuple x (y 2) ∈ funfun) ⇒ (y 1 =: y 2)
    s ["The triple ", m funfunc_, " is often written as ", m $ fun funrel_ fundom_ funimg_]
    s [m fundom_, " is called the ", term "corange", ", ", m funimg_, " is called the ", term "codomain"]
  where
    x = "x"
    y n = "y" !: n

total :: Note
total = ix "total"

totalFunctionDefinition :: Note
totalFunctionDefinition = de $ do
    s ["A ", function, " ", m funfunc_, " is called ", term "total", " if its ", corange, " ", m fundom_, " is equal to the ", domain_, " of ", m funrel_]

totalFunctionNote :: Note
totalFunctionNote = nte $ s ["In literature, ", dquoted "function", " often means ", dquoted "total function"]

surjective :: Note
surjective = ix "surjective"

surjectiveDefinition :: Note
surjectiveDefinition = de $ do
    s ["A ", function, " ", m funfunc_, " is called ", term "surjective", " if its ", codomain, " ", m funimg_, " is equal to the ", image_, " of ", m funrel_]










