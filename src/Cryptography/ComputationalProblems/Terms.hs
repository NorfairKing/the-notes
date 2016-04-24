module Cryptography.ComputationalProblems.Terms where

import           Notes

makeDefs
    [ "problem"
    , "performance"
    , "performance value"
    , "performance function"
    , "solver"
    , "hard"

    , "worst-case problem"
    , "weighted average-case problem"
    , "average-case problem"

    , "reduction"
    , "reduction function"
    , "performance translation function"

    , "deterministic game"
    , "probabillistic game"
    , "game"
    , "player"
    , "winner"
    , "winning condition"

    , "search problem"
    , "instance space"
    , "witness space"
    , "witness"
    , "solution space"

    , "function inversion"
    , "one-way function"

    , "distinction problem"
    , "distinguisher"
    , "advantage"
    , "deterministic distinction game"
    , "distinction game"

    , "discrete logarithm"
    , "DL"

    , "computational Diffie-Hellman"
    , "CDH"

    , "Diffie-Hellman triple"
    , "decisional Diffie-Hellman"
    , "DDH"
    ]

nSolver :: Note -> Note
nSolver n = m n <> "-" <> solver

nSolver' :: Note -> Note
nSolver' n = m n <> "-" <> solver'

eHard :: Note -> Note
eHard e = m e <> "-" <> hard

eHard' :: Note -> Note
eHard' e = m e <> "-" <> hard'

tReduction :: Note -> Note
tReduction t = m t <> "-" <> reduction

tReduction' :: Note -> Note
tReduction' t = m t <> "-" <> reduction'

dProblem :: Note -> Note
dProblem d = m d <> "-" <> problem

dProblem' :: Note -> Note
dProblem' d = m d <> "-" <> problem'
