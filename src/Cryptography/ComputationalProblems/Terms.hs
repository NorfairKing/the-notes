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
    , "reducible"

    , "deterministic game"
    , "probabillistic game"
    , "game"
    , "player"
    , "winner"
    , "winning condition"

    , "function inversion"
    , "function inversion game"
    , "one-way function"

    , "advantage"

    , "distinction problem"
    , "distinguisher"
    , "deterministic distinction game"
    , "distinction game"

    , "bit-guessing problem"
    , "bit guesser"
    , "deterministic bit-guessing game"
    , "bit-guessing game"

    , "search problem"
    , "instance space"
    , "witness space"
    , "witness"
    , "solution space"
    , "deterministic search problem solver"
    , "probabillistic search problem solver"
    , "search problem solver"
    , "deterministic search problem game"
    , "probabillistic search problem game"
    , "search problem game"
    , "success probability"

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

makeThms
    [ "composition of reductions"
    ]
