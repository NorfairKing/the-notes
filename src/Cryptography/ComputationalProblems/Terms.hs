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

    , "game instance"
    , "deterministic game"
    , "winning condition"
    , "probabilistic game"
    , "game"
    , "player"
    , "winner"
    , "deterministic winner"
    , "probabilistic winner"
    , "multi-game"

    , "function inversion"
    , "function inversion game"
    , "one-way function"

    , "advantage"

    , "deterministic distinction problem"
    , "probabilistic distinction problem"
    , "distinction problem"
    , "deterministic distinguisher"
    , "probabilistic distinguisher"
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
    , "probabilistic search problem solver"
    , "search problem solver"
    , "deterministic search problem game"
    , "probabilistic search problem game"
    , "search problem game"
    , "success probability"

    , "deterministic discrete game"
    , "DDS"
    , "monotone binary output"
    , "MBO"
    , "deterministic discrete winner"
    , "DDW"

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

xyDDG :: Note -> Note -> Note
xyDDG x y = m (tuple x y) <> "-" <> deterministicDiscreteGame

yxDDW :: Note -> Note -> Note
yxDDW x y = m (tuple y x) <> "-" <> deterministicDiscreteWinner

makeThms
    [ "composition of reductions"
    , "DL mod two in even order group"
    ]
