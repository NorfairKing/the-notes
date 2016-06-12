module Cryptography.ComputationalProblems.Games.DiscreteGames.Terms where

import           Notes

makeDefs
    [ "discrete game"
    , "deterministic discrete game"
    , "DDS"
    , "monotone binary output"
    , "MBO"
    , "discrete winner"
    , "deterministic discrete winner"
    , "DDW"
    , "probabilistic discrete game"
    , "PDG"
    , "probabilistic discrete winner"
    , "PDW"
    , "deterministic discrete distinguisher"
    , "DDD"
    , "stop symbol"
    , "reduction system"
    , "clonable"
    , "random self-reducible"
    ]

xyDG :: Note -> Note -> Note
xyDG x y = m (tuple x y) <> "-" <> discreteGame

xyDGs :: Note -> Note -> Note
xyDGs x y = m (tuple x y) <> "-" <> discreteGames

yxDW :: Note -> Note -> Note
yxDW y x = m (tuple y x) <> "-" <> discreteWinners

yxDWs :: Note -> Note -> Note
yxDWs y x = m (tuple y x) <> "-" <> discreteWinners

xyDDG :: Note -> Note -> Note
xyDDG x y = m (tuple x y) <> "-" <> deterministicDiscreteGame

yxDDW :: Note -> Note -> Note
yxDDW x y = m (tuple y x) <> "-" <> deterministicDiscreteWinner

xyPDG :: Note -> Note -> Note
xyPDG x y = m (tuple x y) <> "-" <> probabilisticDiscreteGame

yxPDW :: Note -> Note -> Note
yxPDW x y = m (tuple y x) <> "-" <> probabilisticDiscreteWinner

qClonable :: Note -> Note
qClonable q = m q <> "-" <> clonable

qClonable' :: Note -> Note
qClonable' q = m q <> "-" <> clonable'
