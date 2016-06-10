module Cryptography.ComputationalProblems.Games.Terms where

import           Notes

makeDefs
    [ "game instance"
    , "deterministic game"
    , "winning condition"
    , "probabilistic game"
    , "game"
    , "player"
    , "winner"
    , "deterministic winner"
    , "probabilistic winner"
    , "multi-game"
    , "subgame"

    , "function inversion"
    , "function inversion game"
    , "one-way function"

    , "deterministic distinction problem"
    , "probabilistic distinction problem"
    , "distinction problem"
    , "deterministic distinguisher"
    , "probabilistic distinguisher"
    , "distinguisher"
    , "deterministic distinction game"
    , "distinction game"

    , "deterministic bit-guessing problem"
    , "probabilistic bit-guessing problem"
    , "bit-guessing problem"
    , "deterministic bit guesser"
    , "probabilistic bit guesser"
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
    ]

xyDDG :: Note -> Note -> Note
xyDDG x y = m (tuple x y) <> "-" <> deterministicDiscreteGame

yxDDW :: Note -> Note -> Note
yxDDW x y = m (tuple y x) <> "-" <> deterministicDiscreteWinner
