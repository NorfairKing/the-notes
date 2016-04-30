{-# LANGUAGE QuasiQuotes #-}
module Cryptography.ComputationalProblems where

import           Notes                                            hiding
                                                                   (cyclic,
                                                                   inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Composition.Macro
import           Functions.Distances.Terms
import           Functions.Jections.Terms
import           Functions.Order.Terms
import           Groups.Macro
import           Groups.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Probability.Distributions.Macro
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Relations.Orders.Macro
import           Relations.Orders.Terms                           hiding (order)
import           Rings.Macro
import           Rings.Terms
import           Sets.Basics.Terms

import           Cryptography.SymmetricCryptography.Macro
import           Cryptography.SystemAlgebra.AbstractSystems.Macro
import           Cryptography.SystemAlgebra.AbstractSystems.Terms
import           Cryptography.SystemAlgebra.DiscreteSystems.Terms

import           Cryptography.ComputationalProblems.Macro
import           Cryptography.ComputationalProblems.Terms


computationalProblemsS :: Note
computationalProblemsS = section "Computational Problems" $ do
    todo "Restructure this entire section, first abstract problems and performances, then search, etc"
    subsection "Abstract computational problems" $ do
        performanceFunctionDefinition
        subsubsection "Hardness" $ do
            aSolverDefinition
            informationTheoreticalHardness
        subsubsection "Cases" $ do
            worstCaseDefinition
            distributionCaseDefinition
            averageCaseDefinition
            averageCasePerformanceDifference
            probCaseNotation

    subsection "Reductions" $ do
        reductionDefinition
        compositionOfReductions
        todo "generalised reductions for lists of problems"

    subsection "Games" $ do
        deterministicGameDefinition
        probabillisticGameDefinition
        performanceOfAGame

        subsubsection "Distinction problems" $ do
            distinctionProblemDefinition
            distinguisherDefinition
            distinguisherAdvantageDefinition
            distinctionGameDefinition
            distinctionAdvantagePseudoMetric
            distinctionAdvantageRandomVariables

        subsubsection "Bit guessing problems" $ do
            bitGuessingProblemDefinition
            bitGuesserDefinition
            bitGuesserAdvantageDefinition
            bitGuessingGameDefinition
            distinctionBitGuessingEquivalenceLemma

        subsubsection "Search problems" $ do
            searchProblemDefinition
            searchProblemSolverDefinition
            searchProblemGameDefinition
            searchProblemSolverRepetition
            functionInversionDefinition
            oneWayFunctionDefinition


    subsection "Discrete Logarithms" $ do
        discreteLogarithmProblemDefinition
        additiveDLEasy
        dlReducable
        dlModTwoInEvenOrderGroup
        dlNotation
        lsbProbNotation
        dlLSBHardness
        dlRepetitionBoosting

    subsection "Diffie Hellman" $ do
        diffieHellmanTripleDefinition
        computationalDHProblemDefinition
        decisionalDHProblemDefinition

        reductionDlToCDH


performanceFunctionDefinition :: Note
performanceFunctionDefinition = nte $ do
    de $ do
        lab problemDefinitionLabel
        lab solverDefinitionLabel
        lab performanceDefinitionLabel
        lab performanceValueDefinitionLabel
        lab performanceFunctionDefinitionLabel
        let sl = "s"
        s ["Let", m probl_, "be an abstract", problem', and, m solvs_, "a", set, "of abstract", solvers', for, m probl_]
        s ["Let", m perfs_, "be a", set, "of so-called", performanceValues', "associated with", m probl_]
        s ["A", performanceFunction', "is a", function, "as follows"]
        ma $ func perff_ solvs_ perfs_ sl (perf_ sl)
    nte $ do
        s ["Performance values are often real numbers, for example a success", probability, "or a distinguishing", advantage]
        s ["In the simplest case,", performanceValues, "are binary"]

aSolverDefinition :: Note
aSolverDefinition = de $ do
    s ["Let", m probl_, "be a", searchProblem, and, m solvs_, "a", set, "of", solvers, for, m probl_]
    let po = partord_
    s ["Let", m perfs_, "be the", set, performanceValues, "associated with", m probl_, "such that", m perfs_, "is equipped with a", partialOrder, m po]
    let a = "a"
    s ["A", solver, "for which the following holds is called an", nSolver' a, "for", m probl_, "if the following holds"]
    let sl = "s"
    ma $ fa (sl ∈ solvs_) (perf_ sl ⊇: a)

informationTheoreticalHardness :: Note
informationTheoreticalHardness = de $ do
    s ["Let", m probl_, "be a", searchProblem, and, m solvs_, "a", set, "of", solvers, for, m probl_]
    let po = partord_
    s ["Let", m perfs_, "be the", set, performanceValues, "associated with", m probl_, "such that", m perfs_, "is equipped with a", partialOrder, m po]
    let sl = "s"
        e = epsilon
    s ["If every", solver, m sl, "has a", performance, "smaller than some", m e <> ", we call", m probl_, "information-theoreticall", or, "unconditionally", eHard' e]
    ma $ fa (sl ∈ solvs_) (perf_ sl ⊆: e)

worstCaseDefinition :: Note
worstCaseDefinition = de $ do
    lab worstCaseProblemDefinitionLabel
    let p = mathcal "P"
    s ["Let", m p, "be a", set, "of", problems, and, m $ solvs p, "a", set, "of solvers for all of those", problems]
    s ["We define the", worstCaseProblem', m $ spwc p, "as the abstract", problem, "for which any", solver <> "'s", performance, "is defined as the", infimum, "over all the", performances, "of the", solver, "for the", problems, "in", m p]
    let pp = "p"
        sl = "s"
    ma $ perf (spwc p) sl =: infcomp (pp ∈ p) (perf pp sl)

distributionCaseDefinition :: Note
distributionCaseDefinition = de $ do
    let p = mathcal "P"
    s ["Let", m p, "be a", set, "of", problems, and, m $ solvs p, "a", set, "of solvers for all of those", problems]
    let d = "D"
        ppp = "P"
    s ["Let", m d, "be a", probabilityDistribution, "on a", m p <> "-" <> randomVariable, m ppp]
    s ["We define the", weightedAverageCaseProblem', "over", m d, or, dProblem' d, m $ spdc d p, "as the abstract", problem, "for which any", solver <> "'s", performance, "is defined as the weighted average over all the", performances, "of the", solver, "for the", problems, "in", m p, "according to the", distribution, m d]
    let pp = "p"
        sl = "s"
    ma $ perf (spdc d p) sl =: sumcmp (pp ∈ p) (prdsm d pp * perf pp sl)
    s ["In terms of the random variable, that looks as follows"]
    ma $ perf (spdc d p) sl =: sumcmp (pp ∈ p) (prob (ppp =: pp) * perf pp sl)


averageCaseDefinition :: Note
averageCaseDefinition = de $ do
    let p = mathcal "P"
    s ["Let", m p, "be a", set, "of", problems, and, m $ solvs p, "a", set, "of solvers for all of those", problems]
    s ["We define the", averageCaseProblem, "as the", dProblem uniformD_, for, m p]


probCaseNotation :: Note
probCaseNotation = de $ do
    let p = "p"
    s ["Usually many problem can be described as being a specific instance with respect to some key information in what's called an", instanceSpace]
    s ["We then use the following notation"]
    itemize $ do
        item $ do
            s ["We use", m $ spwc p, "to mean", m p, "in the worst-case"]
        item $ do
            let d = "D"
            s ["We use", m $ spdc d p, "to mean", m p, "in the case of the distribution", m d]
        item $ do
            s ["We use", m $ spac p, "to mean", m p, "in the average-case"]


averageCasePerformanceDifference :: Note
averageCasePerformanceDifference = lem $ do
    let p = mathcal "P"
        q = mathcal "Q"
        d = ("D" !:)
        dp = d p
        dq = d q
        oo = perfs ""
    s ["Let", m p, and, m q, "be two", weightedAverageCaseProblems, with, probabilityDistributions, m dp, and, m dq, respectively, "with the same", set, "of", performances, m $ oo ⊆ reals]
    let o = "o"
        o1 = o !: 1
        o2 = o !: 2
        sl = "s"
    ma $ fa sl $ perf p sl <= perf q sl + (pars $ max (cs [o1, o2] ∈ oo) (abs $ o1 - o2)) * statd p q

    toprove

reductionDefinition :: Note
reductionDefinition = do
    let p = "p"
        q = "q"
    de $ do
        lab reductionDefinitionLabel
        lab reductionFunctionDefinitionLabel
        lab performanceTranslationFunctionDefinitionLabel
        s ["Let", m p, and, m q, "be two", problems, and , m $ solvs p, and, m $ solvs q, sets, "of", solvers]
        let po = partord_
        s ["Let", m $ perfs p, and, m $ perfs q, "be the", sets, "of", performanceValues, "associated with", m p, and, m q, "respectively"]
        let pop = po !: p
            poq = po !: q
        s ["Let", m $ perfs p, and, m $ perfs q, "be equipped with the", partialOrders, m pop, and, m poq, "respectively"]
        newline
        let t_ = tau
            t = fn t_
            r_ = rho
            r = fn r_
            sl = "s"
        s ["A", tReduction' t_, "of", m q, to, m p, "is a", function, m r_, "that maps a", solver, for, m p, "onto a", solver, for, m q, ".."]
        ma $ func r_ (solvs p) (solvs q) sl (r sl)
        s ["... such that", m t_, "is a", monotonic', function, "as follows"]
        footnote $ s ["Monotonicity entails that a better", solver, "for", m p, "does not result in a worse", solver, "for", m q]
        let a = "a"
        ma $ func t_ (perfs p) (perfs q) a (t a)
        s [m r_, "is called the", reductionFunction', and, m t_, "is called the", performanceTranslationFunction']
        newline
        s ["The following equation then characterizes this", reduction]
        let (<<) = inposet poq
        ma $ fa (sl ∈ solvs p) $ t (perf p sl) << perf q (r sl)
    nte $ do
        s ["We use a", reduction, "of", m q, to, m p, "to build a", solver, for, m q, "when we have a", solver, for, m p]
    nte $ do
        s ["The characteristic inequality of a reduction of", m q, to, m p, "can be interpreted as implying a lower bound on the performance of any solver for", m q, "in terms of", m p, "or as implying an upper bound on the performance for any solver for", m p, "in terms of", m q]
    de $ do
        lab reducibleDefinitionLabel
        s ["A", problem, m p, "is said to be", reducible, "to another", problem, m q, "if there exists a", reduction, "of", m p, to, m q]


compositionOfReductions :: Note
compositionOfReductions = thm $ do
    let p = "p"
        q = "q"
        r = "r"
    s ["Let", csa [m p, m q, m r], "be three", problems, and, csa [m $ solvs p, m $ solvs q, m $ solvs r], sets, "of", solvers]
    let po = partord_
    s ["Let", csa [m $ perfs p, m $ perfs q, m $ perfs r], "be the", sets, "of", performanceValues, "associated with", csa [m p, m q, m r], "respectively"]
    let pop = po !: p
        poq = po !: q
        por = po !: r
    s ["Let", csa [m $ perfs p, m $ perfs q, m $ perfs r], "be equipped with the", partialOrders, csa [m pop, m poq, m por], "respectively"]
    newline
    let t1_ = tau !: 1
        t1 = fn t1_
        t2_ = tau !: 2
        t2 = fn t2_
        r1_ = rho !: 1
        r1 = fn r1_
        r2_ = rho !: 2
        r2 = fn r2_
        sl = "s"
    s ["Let", m r1_, "be a", tReduction t1_, "of", m q, to, m p, "and let", m r2_, "be a", tReduction t2_, "of", m r, to, m q]
    s ["Then", m $ r2_ ● r1_, "is a", tReduction $ pars $ t2_ ● t1_, "of", m r, to, m p]

    proof $ do
        s ["That", m r1_, "is a", tReduction t1_, "of", m q, to, m p, "means the following"]
        let (<<) = inposet poq
        ma $ fa (sl ∈ solvs p) $ t1 (perf p sl) << perf q (r1 sl)
        let (<.) = inposet por
        s ["Composing both sides with the", monotonic, function, m t2_, "gives us the following"]
        ma $ fa (sl ∈ solvs p) $ t2 (t1 (perf p sl)) <. t2 (perf q (r1 sl))

        s ["That", m r2_, "is a", tReduction t2_, "of", m r, to, m q, "means the following"]
        ma $ fa (sl ∈ solvs q) $ t2 (perf q sl) <. perf r (r2 sl)

        s ["Precomposing both sides with ", m r1_, "gives us the following"]
        ma $ fa (sl ∈ solvs p) $ t2 (perf q (r1 sl)) <. perf r (r2 (r1 sl))

        s ["Combining these two inequalities yields the theorem"]
        ma $ fa (sl ∈ solvs p) $ t2 (t1 (perf p sl)) <. t2 (perf q (r1 sl)) <. perf r (r2 (r1 sl))


deterministicGameDefinition :: Note
deterministicGameDefinition = do
    de $ do
        lab deterministicGameDefinitionLabel
        lab gameDefinitionLabel
        lab playerDefinitionLabel
        let g = gme_
            w = plr_
        s ["A", deterministicGame', m g, "is a", nS 2, "which can at one", interface, "be connected to a", nS 1, m w, "called a", player, or, winner, "and at the other", interface, "outputs a bit (indicating whether or not the game is won)"]
        tikzFig "Deterministic Game System" [] $ raw $ [litFile|src/Cryptography/ComputationalProblems/GameTikZ.tex|]
    nte $ do
        s ["Because a combined", deterministicGame, "-", player, system, "is entirely deterministic, we sometimes view these combined systems under the", injection, "that maps them to the output bit"]

probabillisticGameDefinition :: Note
probabillisticGameDefinition = do
    de $ do
        lab probabillisticGameDefinitionLabel
        let g = gmev_
            w = plrv_
        s ["A", probabillisticGame', m g, "is a", nPS 2, "which can at one", interface, "be connected to a", nPS 1, m w, "called a", player, or, winner, "and at the other", interface, "outputs a bit (indicating whether or not the game is won)"]
    nte $ do
        s ["Because the combination of a", probabillisticGame, anda, player, "can be thought of as a", randomVariable, "in itself, we often view the output bit as a", randomVariable, "as well"]

performanceOfAGame :: Note
performanceOfAGame = de $ do
    s [the, performanceFunction, "of a", deterministicGame, "is defined by viewing its", players, "as solvers"]
    s [the, set, "of", performanceValues, "is", m bits, "and the", performanceFunction, "is defined by whether a", player, "wins the", deterministicGame]
    let g = gme_
        w = plr_
    ma $ func (perff g) (solvs g) bits w $ conv_ g w
    s [the, performanceFunction, "of a", probabillisticGame, "is defined with", m $ ccint 0 1, "as the set of", performanceValues, "as the", performanceFunction, "of the", weightedAverageCaseProblem]
    let gg = gmev_
        ww = plrv_
    ma $ func (perff gg) (solvs ww) bits ww $ (ev $ conv_ gg ww) =: prob (conv_ gg ww =: 1)

searchProblemDefinition :: Note
searchProblemDefinition = do
    de $ do
        lab searchProblemDefinitionLabel
        s ["A", searchProblem', "is a tuple", m sprob_, "consisting of an", instanceSpace', m isp_ <> ",", "a", witnessSpace', or, solutionSpace', m wsp_ <> ",", "a", predicate, m $ fun2 spred_ isp_ wsp_ bits , anda, probabilityDistribution, m sprob_, "over the", instanceSpace]
    nte $ do
        let x = "x"
            w = "w"
        s [the, searchProblem, m sprob_, "consists of finding, for a given instance", m (x ∈ isp_) <> ",", "drawn according to", m sprob_ <> ", a", witness, m (w ∈ wsp_), "such that", m $ sol x w, "holds"]

searchProblemSolverDefinition :: Note
searchProblemSolverDefinition = do
    de $ do
        lab searchProblemSolverDefinitionLabel
        s ["Let", m $ probl_ =: sprob_, "be a", searchProblem]
        s ["A", deterministicSearchProblemSolver', "is a", function, m $ funt isp_ wsp_]
        s ["A", probabillisticSearchProblemSolver', "is a", randomVariable, "over all the", deterministicSearchProblemSolvers, "for the same", searchProblem]
    nte $ do
        s ["The output of a", probabillisticSearchProblemSolver, "for a given instance is a", randomVariable, "over the", witnessSpace, m wsp_]

searchProblemGameDefinition :: Note
searchProblemGameDefinition = de $ do
    lab searchProblemGameDefinitionLabel
    s ["Let", m $ probl_ =: sprob_, "be a", searchProblem]
    let x = "x"
        w = "w"
    s ["A", deterministicSearchProblemGame, for, m probl_, anda, "given instance", m x, "(deterministically) outputs", m x, "at its inside", interface, "and receives a", witness, m w, "at that same", interface]
    s ["It then outputs a set bit (win) if", m $ sol x w, "holds"]
    s ["For a", deterministicSearchProblemGame, "the", performanceValues, "are", m bits]
    newline
    let g = "G"
    s ["A", probabillisticSearchProblemGame, m g, for, m probl_, "is a", randomVariable, "over the", deterministicSearchProblemGames, for, m probl_]
    let sl = "S"
    s ["A solver is then a", probabillisticSearchProblemSolver, m sl]
    s [the, performanceValues, "lie in the interval", m $ ccint 0 1, "and the", performanceFunction, "is defined as follows"]
    let xx = "X"
    ma $ perf g sl =: prob (sol xx (fn sl xx))
    s ["Here", m xx, "is the", randomVariable, "corresponding to the input to the", searchProblemSolver]
    s ["In other words, the", performance, "of a", searchProblemSolver, "is the", probability, "that it finds a valid", witness]

    todo "define advantage independently of game, just for a solver?"

searchProblemSolverRepetition :: Note
searchProblemSolverRepetition = thm $ do
    s ["Simply repeatedly applying the same", probabillisticSearchProblemSolver, "to a given instance of a", searchProblem, "does not necessarily boost the success", probability]
    newline
    let sl = "S"
        sl' = "S'"
        a = alpha
    s ["More formally, let", m sl, "be a", probabillisticSearchProblemSolver, "for a", searchProblem, m sprob_, with, successProbability, m $ a ∈ ocint 0 1, "such that", m spred_, "can be efficiently computed"]
    s ["Let", m sl', "be a", probabillisticSearchProblemSolver, "defined as follows"]
    let x = "x"
        w = "w"
    s ["Given an instance", m $ x ∈ isp_, "it first invokes", m sl, "on input", m x, "to obtain", m w]
    s ["If", m $ sol x w, "holds then", m sl', "returns", m w]
    let w' = "w'"
    s ["Otherwise it invokes", m sl, "again on input", m x, "to obtain", m w', "and returns", m w']
    s ["The best lower bound on the", successProbability, "is", m a]

    proof $ do
        s ["It is easy to see that", m sl', "has", successProbability, "at least", m a]
        s ["Now it suffices to show that there exists a", searchProblem, m sprob_, anda, probabillisticSearchProblemSolver, m sl, "such that", m sl', "has", successProbability, m a, for]
        let x0 = x !: 0
            x1 = x !: 1
        s ["Consider a", searchProblem, "with only two possible instances", m $ wsp_ =: setofs [x0, x1]]
        s ["Let", m sl, "be a", solver, "that finds a valid", witness, "given", m x0, "with probability", m a, "but never finds a valid", witness, "given", m x1]
        s [the, successProbability, "of", m sl, is, m a <> ",but the", successProbability, "of", m sl', "is also", m a]

distinctionProblemDefinition :: Note
distinctionProblemDefinition = de $ do
    lab distinctionProblemDefinitionLabel
    lab distinguisherDefinitionLabel
    let ss = "S"
        s0 = ss !: 0
        s1 = ss !: 1
        p = dprob s0 s1
    s ["An abstract", distinctionProblem', "is a pair of", nSs 1, m $ tuple s0 s1, "and is denoted as", m p]

distinguisherDefinition :: Note
distinguisherDefinition = do
    de $ do
        lab distinguisherDefinitionLabel
        let ss = "S"
            s0 = ss !: 0
            s1 = ss !: 1
            p = dprob s0 s1
        s ["A", distinguisher', "for a", distinctionProblem, m p, "is a", nS 2, "which at one", interface, "connects to a", system, m ss, "(either", m s0, or, m s1 <> ")", "and at the other", interface, "outputs a bit"]
    nte $ do
        s ["A", distinguisher, "can be both deterministic or probabillistic and is therefore usually assumed to be probabillistic"]

distinguisherAdvantageDefinition :: Note
distinguisherAdvantageDefinition = do
    let ss = "S"
        s0 = ss !: 0
        s1 = ss !: 1
        d = "D"
    de $ do
        let p = dprob s0 s1
            ad = dadv d s0 s1
        s [the, advantage', m ad, "of a", distinguisher, m d, "for a", distinctionProblem, m p, "in distinguishing", m s0, and, m s1, "is defined as follows"]
        ma $ ad =: prob (conv_ s1 d =: 1) - prob (conv_ s0 d =: 1)
    nte $ do
        s ["Note that", m $ prob (conv_ s1 d =: 1), and, m $ prob (conv_ s0 d =: 1), "are probabilities in different random experiments"]
        s ["In one experiment the", distinguisher, "is guessing the identity of", m s0, and, "in the other it's guessing the identity of", m s1]
    de $ do
        let dd = mathcal "D"
        s ["We define the", advantage, "of a", set, m dd, "of", distinguishers, "as the", supremum, "of all the individual", distinguishers]
        ma $ dadv dd s0 s1 =: supcomp (d ∈ dd) (dadv d s0 s1)
        s ["Moreover, we denote the", advantage, "of the", set, "of all possible", distinguishers, "as", m $ dadvs s0 s1]

distinctionGameDefinition :: Note
distinctionGameDefinition = de $ do
    lab distinctionGameDefinitionLabel
    let ss = "S"
        s0 = ss !: 0
        s1 = ss !: 1
        p = dprob s0 s1
    s ["A", deterministicDistinctionGame', "for a", distinctionProblem, m p, "(deterministically) outputs either", m s0, or, m s1, "at one", interface, "and receives a bit at that same", interface]
    s ["It then outputs a set bit if the bit that it receives matches the index of the", system, "it outputted before"]
    newline
    s ["A (probabillistic)", distinctionGame', "for a", distinctionProblem, m p, "is a", randomVariable, "over the", deterministicDistinctionGames, "for", m p]

    s ["A", solver, "for a", distinctionGame, "for a", distinctionProblem, m p, "is a", distinguisher, "for", m p]
    s [the, performanceValues, "of such a", solver, "lie in the interval", m $ ccint (-1) 1]
    newline
    s [the, performanceFunction, "is then defined as mapping a", distinguisher, "to its", advantage]

distinctionAdvantagePseudoMetric :: Note
distinctionAdvantagePseudoMetric = lem $ do
    let ss = "S"
        s0 = ss !: 0
        s1 = ss !: 1
        p = dprob s0 s1
        d = mathcal "D"
    s ["If a", set, m d, "of", distinguishers, "for a", distinctionProblem, m p, "is closed under complementing the output bit, then", m $ dadv d cdot_ cdot_, "is a", pseudometric_]

    toprove

distinctionAdvantageRandomVariables :: Note
distinctionAdvantageRandomVariables = lem $ do
    let x = "X"
        y = "Y"
        dom = "A"
    s ["Let", m x, and, m y, "be two", nPSs 1, "that each output only a single value in some", set, m dom, "(and can therefore be thought of as", randomVariables <> ")"]
    s ["The best", distinguisher, "for the", distinctionProblem, m $ dprob x y, "has", advantage, m $ statd x y]
    todo "Does there really exist such a distinguisher or it just an upper bound?"


bitGuessingProblemDefinition :: Note
bitGuessingProblemDefinition = de $ do
    lab bitGuessingProblemDefinitionLabel
    s ["A", bitGuessingProblem', "is a", nS 1, "that outputs a single bit"]

bitGuesserDefinition :: Note
bitGuesserDefinition = de $ do
    lab bitGuesserDefinitionLabel
    s ["A", bitGuesser', "is a", nS 1, "that outputs a single bit at its", interface]

bitGuesserAdvantageDefinition :: Note
bitGuesserAdvantageDefinition = de $ do
    let g = "G"
        b = "B"
    s [the, advantage, "of a", bitGuesser, m g, advantage', "in a", bitGuessingProblem, m b, "is defined as follows"]
    let z = "z"
        zg = z !: g
        zb = z !: b
    s ["Let", m zg, "be the bit output by", m g, and, m zb, "the bit output by", m b]
    ma $ gadv g =: 2 * (pars $ prob (zg =: zb) - (1 / 2))
    s ["The value of the", advantage, "lies in the interval", m $ ccint (-1) 1]

bitGuessingGameDefinition :: Note
bitGuessingGameDefinition = de $ do
    let b = "B"
    s ["A", deterministicBitGuessingGame', "for a", bitGuessingGame, m b, "(deterministically) has", m b, "output its bit and receives a bit at its inside interface from a", player]
    s ["It then outputs a set bit (win) if the two bits equal"]
    newline
    s ["A (probabillistic)", bitGuessingGame', "for a", bitGuessingProblem, m b, "is", game, "is a", randomVariable, "over the deterministic", bitGuessingGames, for, m b]
    s ["A", solver, "for a", bitGuessingGame, "for a", bitGuessingProblem, m b, "is a", bitGuesser, for, m b]
    s [the, performanceValues, "of such a", solver, "lie in the interval", m $ ccint (-1) 1]
    s [the, performanceFunction, "is then defined as mapping a", bitGuesser, "to its", advantage]

distinctionBitGuessingEquivalenceLemma :: Note
distinctionBitGuessingEquivalenceLemma = lem $ do
    s [distinctionProblems, "can be regarded as a special case of", bitGuessingProblems, "where the bit is uniform"]
    proof $ do
        let d = "D"
            b = "B"
        s ["We prove this by showing that for any", distinctionProblem, m d, "there exists a", bitGuessingProblem, m b, "such that every", distinguisher, "for", m d, "can be used to construct a", bitGuesser, for, m b, "with the same (or better)", advantage]
        toprove


dlNotation :: Note
dlNotation = de $ do
    s ["We use", m $ dlp dlgrp_, "to denote the", discreteLogarithm, searchProblem, "in the", group, m dlgrp_]

lsbProbNotation :: Note
lsbProbNotation = de $ do
    let n = "n"
    s ["We use", m $ lsbp n, "to denote the", searchProblem, "of finding the", leastSignificantBit, "of the", discreteLogarithm, "of a", group, element, "in the", group, m $ grp (intmod n) ("" `cdot` ""), "chosen uniformly at random"]

dlLSBHardness :: Note
dlLSBHardness = do
    thm $ do
        let d = delta
            e = epsilon
            sol = "S"
            n = "n"
            p = spac $ lsbp n
            dp = dlpw $ grp (intmod n) $ "" `cdot` ""
            q = "Q"
        s ["For any", m $ cs [d, e] ∈ ccint 0 1, "and for any", solver, m sol, for, m p, with, performance, "greater than", m e <> ",", "there exists a solver", m q, "for", m dp, with, performance, "at least", m $ 1 - d, "which invokes", m sol, "a polynomial number of times (with respect to", csa [m $ log (1 / d), m $ 1 / e, m $ log n] <> ")", "and otherwise performs only a few simple operations"]

        toprove_ "The proof for this will make use of other theorems that still need to be written up on"
    nte $ s ["This theorem is usually worded via its contraposition"]




discreteLogarithmProblemDefinition :: Note
discreteLogarithmProblemDefinition = do
    de $ do
        lab discreteLogarithmDefinitionLabel
        lab dLDefinitionLabel
        let aa = "A"
            a = "a"
            g = "g"
        s [the, discreteLogarithm', "(" <> dL' <> ")", searchProblem, "for a", cyclic_, group, m $ grp_ =: grp (genby g) grpop_, "is the problem of computing, for a given", group, element, m $ aa ∈ grps_, "the exponent", m $ integer a, " such that", m $ aa =: g ^ a, "holds"]
        s ["Formally: let", m grps_, "be the", instanceSpace, "of a", searchProblem, "with", witnessSpace, m $ setsize grps_ <> ",", "the following", predicate, m spred_, "and the uniform instance distribution of", group, elements]
        let x = "x"
            w = "w"
        ma $ (sol x w) ⇔ (g ^ w =: x)
    nte $ do
        s ["Note that the", discreteLogarithm, "for a given", group, and, base, "is also a", functionInversion, searchProblem]

additiveDLEasy :: Note
additiveDLEasy = thm $ do
    let n = "n"
    s [the, discreteLogarithm, "problem is trivially solvable in the", group, m $ intagrp n]
    proof $ do
        let z = "z"
            a = "a"
            g = "g"
        s ["Recall that, for any element", m (z ∈ intmod n) <> ", we are looking for the integer", m $ integer a, "such that", m $ z =: g * a, "where", m g, "is a", generator, "of", m $ intagrp n]
        s ["Luckily, ", m $ intagrp n, "gives rise to a", ring, m $ intring n, "as well"]
        s ["This allows us to find", m a, "by dividing", m z, by, m g]
        s ["More precicely: because", m g, "is a", generator, "means that", m g, "must have a multiplicative inverse in", m $ intring n, "otherwise no multiple of", m g, "would be equal to", m 1]
        s ["Now the only thing we need to do is go through the", elements, "of", m $ intmod n, "multiply each of them by", m g, "in", m $ intring n, "and check if the result equals", m 1, "to find the multiplicative inverse", m $ rinv g, "of", m g, "in", m $ intring n]
        s ["We then compute", m a, "by evaluating", m $ rinv g * z =: rinv g * g * a =: a]
        s ["We could also use the extended Euclidean algorithm to find", m $ rinv g, "even more efficiently"]
        refneeded "Extended Euclidean algorithm"

dlReducable :: Note
dlReducable = thm $ do
    let g = "g"
        h = "h"
    s [the, discreteLogarithm, "problem in a", group, m grp_, "for a", generator, m g, "is reducable to the", discreteLogarithm, "problem in that same", group, "but for a different", generator]

    proof $ do
        let a = "A"
        s ["Let", m a, "be an algorithm that solves the", discreteLogarithm, "problem for a", generator, m g]
        s ["We construct an algorithm that solves the", discreteLogarithm, "problem for another", generator, m h, "of", m grp_, "as follows"]
        let z = "z"
            b = "b"
            c = "c"
        s ["Let", m z, "be the", group, element, "that we want the", discreteLogarithm, m b, "base", m h, "in", m grp_, "of"]
        s ["There then exists a", m $ integer c, "such that", m c, "is the", discreteLogarithm, "base", m g, "in", m grp_, "of", m z]
        ma $ z =: h ^ b =: g ^ c
        let d = "d"
        s ["Because", m h, "is an", element, "of", m grps_ <> ",", "there exists a", m $ integer d, "such that", m $ h =: g ^ d, "holds"]
        ma $ z =: (pars $ g ^ d) ^ b =: g ^ c
        s ["This means that we have the following equation for", m c, "in", m $ intring $ ord grps_]
        ma $ d * b =: c
        s ["The algorithm now uses", m a, "to find", m c, from, m z, and, m d, from, m h]
        s ["It then computes the multiplicative inverse of", m d, "in", m $ intring $ ord grps_, "with the extended Euclidean algorithm and finally computes", m b, "by evaluating", m $ rinv d * c =: rinv d * d * b =: b]

dlModTwoInEvenOrderGroup :: Note
dlModTwoInEvenOrderGroup = thm $ do
    let n = "n"
    s ["Let", m grp_, beA, group, with, "an even", order, m $ ord grp_ =: 2 * n]
    s ["There exists an efficient algorithm to compute whether the", discreteLogarithm, "of an", element, "is even or not"]

    proof $ do
        let x = "x"
        s ["Let", m x, beAn, element, "of", m grps_]
        let g = "g"
            a = "a"
        s ["For a given base", m g, "the task is to compute", m $ a `mod` 2, "such that", m $ x =: g ^ a, "holds"]
        let q = "q"
            r = "r"
        s ["Define", m q, and, m r, "as the quotient and rest after division by", m 2, "of", m a]
        s ["Observe first the following"]
        ma $ x ^ n =: g ^ (a * n) =: g ^ ((pars $ 2 * q + r) * n) =: g ^ (2 * n * q) ** (g ^ (r * n) =: g ^ (r * n))
        s ["This means that", m $ x ^ n, "will be equal to the", neutralElement, "if", m a, "is even and", m $ g ^ n, "(which cannot be the", neutralElement, "because", m g, "is a", generator, and, m grp_, "has", order, m (2 * n) <> ") if", m a, "is odd"]
        s ["We only have to compare", m $ x ^ n, "to the", neutralElement, "to determine", m $ a `mod` 2]


dlRepetitionBoosting :: Note
dlRepetitionBoosting = thm $ do
    let g = "g"
        grp_ = grp (genby g) grpop_
    s ["Let", m grp_, "be a", cyclic, group]
    let sl = "S"
        sl' = "S'"
        a = alpha
    s ["If there exists a", probabillisticSearchProblemSolver, m sl, for, m $ dlp grp_, with, successProbability, m a <> ",", "then it can be used to build a", probabillisticSearchProblemSolver, m sl', with, successProbability, "strictly greater than", m a]

    toprove



diffieHellmanTripleDefinition :: Note
diffieHellmanTripleDefinition = de $ do
    lab diffieHellmanTripleDefinitionLabel
    let a = "a"
        b = "b"
        g = "g"
    s ["A", diffieHellmanTriple', "in a given", cyclic, group, m $ grp_ =: grp (genby g) grpop_, "is a triple of the form", m $ triple (g ^ a) (g ^ b) (g ^ (a * b)), "where", m a, and, m b, "are whole numbers"]

computationalDHProblemDefinition :: Note
computationalDHProblemDefinition = de $ do
    lab computationalDiffieHellmanDefinitionLabel
    lab cDHDefinitionLabel
    let a = "a"
        b = "b"
        g = "g"
        grp_ = grp (genby g) grpop_
        ga = g ^ a
        gb = g ^ b
        gab = g ^ (a * b)
    s [the, computationalDiffieHellman, "(" <> cDH' <> ")", "problem for a given", cyclic, group, m grp_, "is the problem of computing, for given group elements", m ga, and, m gb, "the group element", m gab]
    newline
    s ["More formally,", m $ cdhp grp_, "is the", nS 2, "that outputs", m $ triple g ga gb, "at its inside", interface, "and outputs", m 1, "at its outside", interface, "if it subsequently receives", m gab, "at that", interface]

decisionalDHProblemDefinition :: Note
decisionalDHProblemDefinition = de $ do
    lab computationalDiffieHellmanDefinitionLabel
    lab cDHDefinitionLabel
    let a = "a"
        b = "b"
        c = "c"
        g = "g"
        grp_ = grp (genby g) grpop_
        ga = g ^ a
        gb = g ^ b
        gc = g ^ c
        gab = g ^ (a * b)
    s [the, decisionalDiffieHellman', "(" <> dDH' <> ")", "problem for a given", cyclic, group, m grp_, "is the problem of determining whether, for given group elements", (m ga) <> ",", m gb, and, m gc, "whether they are chosen randomly and independently from", m grps_, "or form a", diffieHellmanTriple]
    newline
    let t = "T" !: grp_
        r = "R" !: grp_
    s ["More formally,", m $ ddhp grp_, "is the", distinctionProblem, m $ dprob t r, "between two", nPSs 1, m t, and, m r]
    itemize $ do
        item $ do
            let tab = t !: cs [a, b]
            s [m t, "is the", nPS 1, "that is the", randomVariable, "with uniform distribution over the", nDSs 1, m tab, "that output", m $ triple ga gb gab, "and at their", interface, "and do nothing else"]
            s ["Here", m a, and, m b, "are", elements, "of", m $ intmod $ setsize grps_]
        item $ do
            let rabc = r !: cs [a, b, c]
            s [m r, "is the", nPS 1, "that is the", randomVariable, "with uniform distribution over the", nDSs 1, m rabc, "that output", m $ triple a b c, "at their", interface, "and do nothing else"]
            s ["Here", csa [m a, m b, m c], "are", elements, "of", m grps_]


reductionDlToCDH :: Note
reductionDlToCDH = thm $ do
    let g = "g"
        grp_ = grp (genby g) grpop_
    s ["For a given", cyclic, group, m grp_ <> ",", "the", discreteLogarithm, problem, m $ dlp grp_, is, reducible, "to the", computationalDiffieHellman, problem, m $ cdhp grp_]

    toprove



functionInversionDefinition :: Note
functionInversionDefinition = de $ do
    lab functionInversionDefinitionLabel
    let a = "A"
        b = "B"
        f_ = "f"
        f = fn f_
    s ["Let", m $ fun f_ a b, "be a", function]
    s [the, functionInversion', "problem", for, m f_, "is the", searchProblem, m $ sprob b a spred_ sppd_, "where", m spred_, "is a", predicate, "defined as follows and", m sppd_, "is some distribution of", m b]
    let x = "x"
        w = "w"
    ma $ (sol x w) ⇔ (f w =: x)


oneWayFunctionDefinition :: Note
oneWayFunctionDefinition = de $ do
    s ["A", oneWayFunction', "is a", function, "such that its", functionInversion, searchProblem, "is computationally hard"]











