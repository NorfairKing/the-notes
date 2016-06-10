module Cryptography.ComputationalProblems.Games.DiscreteGames.Terms where

import           Notes

makeDefs
    [ "deterministic discrete game"
    , "DDS"
    , "monotone binary output"
    , "MBO"
    , "deterministic discrete winner"
    , "DDW"
    , "probabilistic discrete game"
    , "PDG"
    , "probabilistic discrete winner"
    , "PDW"
    , "deterministic discrete distinguisher"
    , "DDD"
    , "stop symbol"
    ]

xyDDG :: Note -> Note -> Note
xyDDG x y = m (tuple x y) <> "-" <> deterministicDiscreteGame

yxDDW :: Note -> Note -> Note
yxDDW x y = m (tuple y x) <> "-" <> deterministicDiscreteWinner

xyPDG :: Note -> Note -> Note
xyPDG x y = m (tuple x y) <> "-" <> probabilisticDiscreteGame

yxPDW :: Note -> Note -> Note
yxPDW x y = m (tuple y x) <> "-" <> probabilisticDiscreteWinner
