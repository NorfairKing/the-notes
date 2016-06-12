module Cryptography.ComputationalProblems.Games.HardnessAmplification where

import           Notes

import           Probability.Independence.Terms

import           Cryptography.ComputationalProblems.Games.Abstract.Terms

import           Cryptography.ComputationalProblems.Games.HardnessAmplification.Macro
-- import Cryptography.ComputationalProblems.Games.HardnessAmplification.Terms

hardnessAmplificationSSS :: Note
hardnessAmplificationSSS = subsubsection "Hardness amplification for games" $ do
    combiningGamesDefinition

combiningGamesDefinition :: Note
combiningGamesDefinition = de $ do
    let k = "k"
        g = "G"
        (g1, g2, gk, gs) = buildList g k
    s ["Let", m gs, "be a", m k, independent, games]
    s ["We can combine these into a single game by requesting that all games be won"]
    s ["We denote this games as follows"]
    ma $ andgamelist g1 g2 gk
