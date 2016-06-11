{-# LANGUAGE QuasiQuotes #-}
module Cryptography.ComputationalProblems.Games.DiscreteGames where

import           Notes                                                        hiding (cyclic, inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Logic.FirstOrderLogic.Macro
import           Probability.RandomVariable.Macro
import           Sets.Basics.Terms

import           Cryptography.SymmetricCryptography.Macro
import           Cryptography.SystemAlgebra.AbstractSystems.Macro
import           Cryptography.SystemAlgebra.DiscreteSystems.Terms

import           Cryptography.ComputationalProblems.Abstract.Macro
import           Cryptography.ComputationalProblems.Abstract.Terms
import           Cryptography.ComputationalProblems.Reductions.Macro
import           Cryptography.ComputationalProblems.Reductions.Terms

import           Cryptography.ComputationalProblems.Games.Abstract.Macro
import           Cryptography.ComputationalProblems.Games.Abstract.Terms

import           Cryptography.ComputationalProblems.Games.DiscreteGames.Macro
import           Cryptography.ComputationalProblems.Games.DiscreteGames.Terms


discreteGamesSSS :: Note
discreteGamesSSS = subsubsection "Discrete games" $ do
    discreteGameDefinition
    discreteGameWinnerDefinition
    probabilisticDiscreteGameDefinition
    probabilisticDiscreteGameWinnerDefinition
    deterministicDiscreteDistinguisherDefinition
    discreteGamesAsGamesDefinition
    discreteGamePerformanceDefinition
    paragraph "reductions for games" $ do
        reductionSystemDefinition
        reductionMultipleInvocationDefinition

discreteGameDefinition :: Note
discreteGameDefinition = do
    de $ do
        let xx = mathcal "X"
            yy = mathcal "Y"
            i = "i"
            ai = "a" !: i
        s ["A", deterministicDiscreteGame', or, dDS', "can be described as a", xyDS xx yy, "that, in addition to outputing an", element, "of", m yy, "upon receival of an input", element, "of", m xx, ", also outputs a bit", m ai, "indicating whether the game has been won"]
        s ["The bit is monotone in the sense that it is initally set to", m 0 <> ", changes to", m 1, "once the game is won and never changes back"]
        s ["For", xyDS xx (yy ⨯ bits) <> ", the binary component of the output is called a", monotoneBinaryOutput', or, mBO']
        s ["Such a", deterministicDiscreteSystem, "with a", monotoneBinaryOutput, "is called an", xyDDG xx yy]
    tikzFig "Discrete game" [] $ raw $ [litFile|src/Cryptography/ComputationalProblems/Games/GameTikZ.tex|]
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

discreteGamesAsGamesDefinition :: Note
discreteGamesAsGamesDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
        gg = "G"
        ww = "W"
    s ["A", yxDW yy xx, m ww, "is said to win a", xyDG xx yy, m gg, "if the", mBO, "of the", discreteGame, "ever becomes", m 1, "when it is connected to the", discreteWinner]
    let i = "i"
        ai = "a" !: i
    ma $ wins gg ww =: 1 === (te i $ ai =: 1)

discreteGamePerformanceDefinition :: Note
discreteGamePerformanceDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
        gg = "G"
        ww = "W"
    s ["When an", xyDG xx yy, m gg, "is seen as a", problem, "we can view its", yxDW yy xx, as, solvers, "and defined the following", performanceFunction]
    todo "Split into four for the different cases"
    ma $ func (perff gg) (prdss ww) (ccint 0 1) (prdis_ ww) (perf gg (prdis_ ww) =: prdiss [ww, gg] (wins gg ww =: 1))

reductionSystemDefinition :: Note
reductionSystemDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
        uu = mathcal "U"
        vv = mathcal "V"
        gg = "G"
        hh = "H"
        ww = "W"
        cc = "C"
    s ["Let", m gg, "be a", xyDG xx yy, and, m hh, a, xyDG uu vv]
    s ["Recall that a", reduction, "is a", function, "that maps", yxDWs yy xx, onto, yxDWs vv uu]
    s ["A so-called", defineTerm "reduction by a converter", m red_, from, m gg, to, m hh, "is a", function, "that connects a", uvxyC uu vv xx yy, m cc, "to a", yxDW uu vv, "to form a", yxDW yy xx]
    s ["We denote this", reductionFunction, as, m $ tred_ cc]
    tikzFig "Discrete game" [] $ raw $ [litFile|src/Cryptography/ComputationalProblems/Games/ReductionSystemTikZ.tex|]
    s ["We then have the following", reduction, "equation"]
    ma $ fa ww $ perf (conv_ gg cc) ww =: perf gg (tred cc ww) =: perf gg (conv_ cc ww)

reductionMultipleInvocationDefinition :: Note
reductionMultipleInvocationDefinition = de $ do
    let q = "q"
    s ["The second kind of", reduction, "is by multiple", "(" <> m q <> ")", "invocation of a solver"]
    let ww = "W"
    s [the, reductionFunction, "then maps a", winner, m ww, to, m $ icop ww q]
    s ["This", reductionFunction, m red_, "is then denoted as", m $ mred_ q]
    ma $ fn (mred_ q) ww =: mred ww q
