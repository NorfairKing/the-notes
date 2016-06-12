{-# LANGUAGE QuasiQuotes #-}
module Cryptography.ComputationalProblems.Games.DiscreteGames where

import           Notes                                                        hiding (cyclic, inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Logic.FirstOrderLogic.Macro
import           Probability.Independence.Terms
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Relations.Orders.Macro
import           Sets.Basics.Terms

import           Cryptography.SymmetricCryptography.Macro

import           Cryptography.SystemAlgebra.AbstractSystems.Macro
import           Cryptography.SystemAlgebra.AbstractSystems.Terms
import           Cryptography.SystemAlgebra.DiscreteSystems.Macro
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
    equivalentGamesLemma

    paragraph "reductions for games" $ do
        reductionSystemDefinition
        reductionMultipleInvocationDefinition

        performanceAmplificationByRepetition
        cloningGameSystems
        randomSelfReduction
        combiningClonabilityAndRandomSelfReduction
        reductionNote

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
    lab reductionSystemDefinitionLabel
    s ["Let", m gg, "be a", xyDG xx yy, and, m hh, a, xyDG uu vv]
    s ["Recall that a", reduction, "is a", function, "that maps", yxDWs yy xx, onto, yxDWs vv uu]
    s ["A so-called", defineTerm "reduction by a converter", m red_, from, m gg, to, m hh, "is a", function, "that connects a", uvxyC uu vv xx yy, m cc, "to a", yxDW uu vv, "to form a", yxDW yy xx]
    s ["We denote this", reductionFunction, as, m $ tred_ cc]
    tikzFig "Discrete game" [] $ raw $ [litFile|src/Cryptography/ComputationalProblems/Games/ReductionSystemTikZ.tex|]
    s ["We then have the following", reductionSystem, "equation"]
    ma $ fa ww $ perf (conv_ gg cc) ww =: perf gg (tred cc ww) =: perf gg (conv_ cc ww)

reductionMultipleInvocationDefinition :: Note
reductionMultipleInvocationDefinition = de $ do
    let q = "q"
    s ["The second kind of", reduction, "is by multiple", "(" <> m q <> ")", "invocation of a solver"]
    let ww = "W"
    s [the, reductionFunction, "then maps a", winner, m ww, to, m $ icop ww q]
    s ["This", reductionFunction, m red_, "is then denoted as", m $ mred_ q]
    ma $ fn (mred_ q) ww =: mred ww q

equivalentGamesLemma :: Note
equivalentGamesLemma = lem $ do
    s ["Two", games, "are equivalent if they have the same", performanceFunction]

performanceAmplificationByRepetition :: Note
performanceAmplificationByRepetition = do
    let q = "q"
        x = "x"
    s ["Let", m $ psiq q x, "denote the", probability, "that, among", m q, independent, "binary", randomVariables <> ", each of which is", m 1, with, probability, m x <> ", at least one of them is", m 1]
    ma $ psiq q x =: 1 - (pars $ 1 - x) ^ q
    s ["We also define the inverse function", m $ chiq q cdot_]
    ma $ chiq q x =: 1 - (pars $ 1 - x) ^ (1 / q)
    s ["Note that the following inequality holds"]
    why
    ma $ chiq q x <= ((- ln (1 - x)) / q)

    let gg = "G"
    lem $ do
        s ["Let", m gg, "be a", discreteGame]
        let ww = "W"
        ma $ fa ww $ perf (orgame $ icop gg q) (mred ww q) =: psiq q (perf gg ww)

        proof $ do
            s ["If", m $ mred ww q, "is connected to", m $ icop gg q, "then this corresponds to", m q, independent, "copies of", m ww, "connected to", m gg, "and the", m q, mBOs, "of the", m q, "copies of", m gg, "are hence", independent, "bits, each of which is equal to", m 1, with, probability, m $ perf gg ww]
            s ["Hence their logical OR is", m 1, with, probability, m $ psiq q (perf gg ww)]
    nte $ do
        s ["The above reduction only works for", independent, "copies of", m gg]
        s ["However, what one actually wants is to amplify the performance of a given instance of a", game]

cloningGameSystems :: Note
cloningGameSystems = do
    let q = "q"
        gg = "G"
        kk = "K"
    de $ do
        s ["A", discreteGame, "is called", qClonable' q, "by a", converter, m kk, "if attaching", m kk, to, m gg, "results in a", system, "equivalent to", m $ orgame $ clon gg q]
        ma $ conv_ kk gg `eqsys` orgame (clon gg q)
    nte $ do
        s ["A cloning", converter, m kk, "can typically be defined as emulating", m q, "copies of", m gg, "at the left", interface <> ", intneracting with a", winner, for, m $ orgame (clon gg q), "checking any obtained solution for one of the subgames for correctness and then forwarding a correctsolution, if there is any, at the right", interface, to, m gg]
        s ["If", m gg, "is won, this means that one of the clones of", m gg, "was won, i.e., that", m $ orgame (clon gg q), "is won"]
        let ww = "W"
        ma $ fa ww $ perf (conv_ kk gg) ww =: perf (orgame (clon gg q)) ww

randomSelfReduction :: Note
randomSelfReduction = do
    let g = "g"
        gg = "G"
        ggg = mathcal "G"
        rr = "R"
        ww = "W"
    de $ do
        s ["A", probabilisticDiscreteGame, m gg <> ", defined as a", probabilityDistribution, over, a, set, m ggg, "of", deterministicDiscreteGames, "(the instance set)", "is called", randomSelfReducible', by, converter, m rr, "if cenecting", m rr, "to any instance", m g, "results in a", system, "equivalent to", m gg]
        ma $ fa (g ∈ ggg) $ conv_ g rr `eqsys` gg

    lem $ do
        s ["If a", probabilisticDiscreteGame, m gg, is, randomSelfReducible, by, converter, m rr, "then an average-case winner can be transformed into a worst-case winner with the same success", probability]
        s ["Let", m $ spwc ggg, "be the worst-case", game, "over an instance", set, m ggg, and, m $ spac gg, "the average-case", game, "over that same instance", set]
        ma $ fa ww $ perf (conv_ (spwc (ggg)) rr) ww =: perf (spac gg) ww

        proof $ do
            s ["For every instance", m $ g ∈ ggg, "and every", winner, m ww, "we find the following from the definition of", randomSelfReducible]
            ma $ perf g (conv_ rr ww) =: perf (spac gg) ww
            s ["Now the theorem follows linearly"]
            ma $ perf (spwc ggg) (conv_ ww rr)
                    =: infcomp (g ∈ ggg) (perf g (conv_ ww rr))
                    =: infcomp (g ∈ ggg) (perf (spac gg) ww )
                    =: perf (spac gg) (ww)

combiningClonabilityAndRandomSelfReduction :: Note
combiningClonabilityAndRandomSelfReduction = thm $ do
    let gg = "G"
        rr = "R"
        kk = "K"
        q = "q"
    s ["Let", m gg, be, randomSelfReducible, by, m rr, and, clonable, by, m kk <> ", then, for any", m q, ", the following", reductionFunction, m red_, "admits a", tReduction $ psiq q cdot_]
    let ww = "W"
    ma $ red ww =: conv_ (conv_ kk (icop rr q)) (icop ww q)
    ma $ fa ww $ perf gg (red ww) =: psiq q (perf gg (ww))

    proof $ do
        s ["Because", m gg, is, randomSelfReducible, by, m rr, "we have the following equivalence"]
        ma $ conv_(clon gg q) (icop rr q) `eqsys` (icop gg q)
        s ["Consequently also the following equality holds"]
        ma $ fa ww $
            perf (orgame $ clon gg q) (conv_ (icop rr q) ww)
         =: perf (orgame $ conv_ (clon gg q) (icop rr q)) ww
         =: perf (orgame $ icop gg q) ww
        s ["This sais that we can generate", m q, "independent copies of", m gg, "by cloning", m gg, m q, "times and applying the", m rr, "converter to each of clones"]
        s ["Now we use the clonability of", m gg, by, m kk]
        ma $ conv_ gg kk `eqsys` orgame (clon gg q)
        s ["Combining these equations yields the theorem as follows"]
        s ["Let", m ww, "be an arbitrary winner and use the reduction system equation" <> ref reductionSystemDefinitionLabel]
        aligneqs (perf gg (red ww))
            [ perf gg (conv_ (conv_ kk (icop rr q)) (icop ww q))
            , perf (conv_ gg kk) (conv_ (icop rr q) (icop ww q))
            , perf (orgame $ clon gg q) (conv_ (icop rr q) (icop ww q))
            , perf (orgame $ icop gg q) (icop ww q)
            , psiq q $ perf gg ww
            ]


reductionNote :: Note
reductionNote = nte $ do
    let gg = "G"
        p = "p"
        q = "q"
    s ["This means that if a", game, m gg, is, "efficiently", randomSelfReducible, "and if there exists no efficient winner for", m gg, "with probability", m p, "then this implies that no efficient winner can win", m gg, with, probability, m $ chiq q p]
    s ["We can make this", m q, "arbitrarily large (and thus", m $ chiq q p, "arbitrarily small) as long as the random self-reduction stays efficient while doing so"]

