module Cryptography.ComputationalProblems.Terms where

import           Notes

makeDefs
    [ "search problem"
    , "instance space"
    , "witness space"
    , "witness"
    , "solution space"

    , "function inversion"
    , "one-way function"

    , "discrete logarithm"
    , "DL"

    , "distinction problem"

    , "computational Diffie-Hellman"
    , "CDH"

    , "Diffie-Hellman triple"
    , "decisional Diffie-Hellman"
    , "DDH"

    , "game"
    , "winning condition"
    , "solver"
    , "performance"
    , "performance value"
    , "performance function"
    , "hard"
    , "reduction"
    , "reduction function"
    , "performance translation function"
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
