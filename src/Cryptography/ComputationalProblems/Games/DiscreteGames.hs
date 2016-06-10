{-# LANGUAGE QuasiQuotes #-}
module Cryptography.ComputationalProblems.Games.DiscreteGames where

import           Notes                                                        hiding (cyclic, inverse)

import           Sets.Basics.Terms

import           Cryptography.SymmetricCryptography.Macro
import           Cryptography.SystemAlgebra.DiscreteSystems.Terms

import           Cryptography.ComputationalProblems.Games.DiscreteGames.Macro
import           Cryptography.ComputationalProblems.Games.DiscreteGames.Terms


discreteGamesSSS :: Note
discreteGamesSSS = subsubsection "Discrete games" $ do
    discreteGameDefinition
    discreteGameWinnerDefinition
    probabilisticDiscreteGameDefinition
    probabilisticDiscreteGameWinnerDefinition
    deterministicDiscreteDistinguisherDefinition

discreteGameDefinition :: Note
discreteGameDefinition = do
    de $ do
        let xx = mathcal "X"
            yy = mathcal "Y"
        s ["A", deterministicDiscreteGame', or, dDS', "can be described as a", xyDS xx yy, "that, in addition to outputing an", element, "of", m yy, "upon receival of an input", element, "of", m xx, ", also outputs a bit indicating whether the game has been won"]
        s ["The bit is monotone in the sense that it is initally set to", m 0 <> ", changes to", m 1, "once the game is won and never changes back"]
        s ["For", xyDS xx (yy ⨯ bits) <> ", the binary component of the output is called a", monotoneBinaryOutput', or, mBO']
        s ["Such a", deterministicDiscreteSystem, "with a", monotoneBinaryOutput, "is called an", xyDDG xx yy]
    tikzFig "Discrete game" [] $ raw $ [litFile|src/Cryptography/ComputationalProblems/GameTikZ.tex|]
    nte $ do
        s ["Intuitively, this", mBO, "represent whether the", deterministicDiscreteGame, "has been won"]

discreteGameWinnerDefinition :: Note
discreteGameWinnerDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
    s ["A", deterministicDiscreteWinner', or, dDW', yxDDW yy xx, "for a", xyDDG xx yy, "is a", yxDE yy xx]
    s ["A", dDW, "is generally understood not to receive the 'wins' bit"]


probabilisticDiscreteGameDefinition :: Note
probabilisticDiscreteGameDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
    s ["A", probabilisticDiscreteGame', or, pDG', xyPDG xx yy, "is analogously similar to a", xyPS xx yy]

probabilisticDiscreteGameWinnerDefinition :: Note
probabilisticDiscreteGameWinnerDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
    s ["A", probabilisticDiscreteWinner', or, pDW', yxPDW yy xx, "for a", xyPDG xx yy, "is a", yxPE yy xx]
    s ["A", pDW, "is generally understood not to receive the 'wins' bit"]

deterministicDiscreteDistinguisherDefinition :: Note
deterministicDiscreteDistinguisherDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
    s ["A", deterministicDiscreteDistinguisher', "for", xySs xx yy, "is an environment for", xySs xx yy, "which, when it stops, also outputs a bit"]
    s ["More formally, it is an environment with two so-called", stopSymbols', m $ stopsym 0, and, m $ stopsym 1]
    clarify "environment?"
