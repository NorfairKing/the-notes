module Cryptography.ComputationalProblems.Reductions.Terms where

import           Notes

makeDefs
    [ "reduction"
    , "reduction function"
    , "performance translation function"
    , "reducible"
    ]

tReduction :: Note -> Note
tReduction t = m t <> "-" <> reduction

tReduction' :: Note -> Note
tReduction' t = m t <> "-" <> reduction'

makeThms
    [ "composition of reductions"
    ]
