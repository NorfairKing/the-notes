module Functions.Basics (
          functionBasics

        , function              , function_
        , partialFunction       , partialFunction_
        , corange               , corange_
        , codomain              , codomain_

        , total                 , total_
        , surjective            , surjective_

        , binaryFunction        , binaryFunction_
        , ternaryFunction       , ternaryFunction_

        , memberWiseApplication , memberWiseApplication_

        , scottContinuous       , scottContinuous_
    ) where

import           Notes

import           Sets.Basics                (subset)

import           Relations.BasicDefinitions (relation_)
import           Relations.Domain           (domain_, image_)

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
    , "Scott-continuous"
    ]

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
    ternaryFunctionDefinition

    memberwiseApplication

    scottContinuousFunctionDefinition


partialFunctionDefinition :: Note
partialFunctionDefinition = de $ do
    s ["A ", partialFunction', or, function', " ", m funfun, " is a triple ", m t , " where ", m fundom_, and, funimg_, " are sets and ", m funrel_, " is a single-valued binary ", relation_, " between ", m fundom_, and, m funimg_]
    s ["Each of the sets ", m fundom_, and, funimg_, " have an equivalence relation defined on them, both written as ", m (eqsign)]
    ma $ fa (cs [x, y 1, y 2]) $ (pars $ tuple x (y 1) ∈ funfun ∧ tuple x (y 2) ∈ funfun) ⇒ (y 1 =: y 2)
    s ["The triple ", m t, " is often written as ", m $ fun funrel_ fundom_ funimg_]
    s [m fundom_, " is called the ", corange', ", ", m funimg_, " is called the ", codomain']
  where
    x = "x"
    y n = "y" !: n
    t = (triple funrel_ fundom_ funimg_)

totalFunctionDefinition :: Note
totalFunctionDefinition = de $ do
    s ["A ", function, " ", m funfunc_, " is called ", total', " if its ", corange, " ", m fundom_, " is equal to the ", domain_, " of ", m funrel_]

totalFunctionNote :: Note
totalFunctionNote = nte $ s ["In mathematical literature, ", dquoted "function", " often means ", dquoted "total function"]

surjectiveDefinition :: Note
surjectiveDefinition = de $ do
    s ["A ", function, " ", m funfunc_, " is called ", surjective', " if its ", codomain, " ", m funimg_, " is equal to the ", image_, " of ", m funrel_]



binaryFunctionDefinition :: Note
binaryFunctionDefinition = de $ do
    lab binaryFunctionDefinitionLabel
    s ["A ", binaryFunction', " is a function ", m (fun funrel_ fundom_ funimg_), " where ", m fundom_, " is a set of tuples"]


ternaryFunctionDefinition :: Note
ternaryFunctionDefinition = de $ do
    lab ternaryFunctionDefinitionLabel
    s ["A ", ternaryFunction', " is a function ", m (fun funrel_ fundom_ funimg_), " where ", m fundom_, " is a set of triples"]

memberwiseApplication :: Note
memberwiseApplication = de $ do
    s ["Let ", m funfunc_, " be a ", function]
    s [the, memberWiseApplication', " of ", m funfunc_, " to a ", subset, " ", m ss, " of ", m fundom_, " is the set of all applications of ", m funrel_, " to members of ", m ss, " and is denoted as ", m (funrel_ `mwfn` ss)]
    ma $ funrel_ `mwfn` ss === setcmpr (funrel_ `fn` e) (e ∈ ss)
  where
    ss = "S"
    e = "s"

scottContinuousFunctionDefinition :: Note
scottContinuousFunctionDefinition = mempty $ de $ do -- TODO(kerckhove) finish this
    lab scottContinuousDefinitionLabel
    s ["A ", function, " is called ", scottContinuous']

