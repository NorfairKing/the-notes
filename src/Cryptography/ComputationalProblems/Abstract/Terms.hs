module Cryptography.ComputationalProblems.Abstract.Terms where

import           Notes

makeDefs
    [ "problem"
    , "performance"
    , "performance value"
    , "performance function"
    , "solver"
    , "hard"
    , "advantage"

    , "worst-case problem"
    , "weighted average-case problem"
    , "average-case problem"
    ]

nSolver :: Note -> Note
nSolver n = m n <> "-" <> solver

nSolver' :: Note -> Note
nSolver' n = m n <> "-" <> solver'

eHard :: Note -> Note
eHard e = m e <> "-" <> hard

eHard' :: Note -> Note
eHard' e = m e <> "-" <> hard'

dProblem :: Note -> Note
dProblem d = m d <> "-" <> problem

dProblem' :: Note -> Note
dProblem' d = m d <> "-" <> problem'

