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
import           Functions.Order.Terms
import           Groups.Macro
import           Groups.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           NumberTheory.Macro
import           NumberTheory.Terms
import           Probability.Distributions.Macro
import           Probability.Independence.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Relations.Orders.Macro
import           Relations.Orders.Terms                           hiding (order)
import           Rings.Macro
import           Rings.Terms
import           Sets.Basics.Terms
import           Sets.Partition.Terms

import           Cryptography.SymmetricCryptography.Macro
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
        reductionReeinterpretation
        compositionOfReductions
        todo "generalised reductions for lists of problems"

    subsection "Games" $ do
        deterministicGameDefinition
        performanceOfDeterministicWinnerInDeterministicGame
        probabillisticWinnerDefinition
        performanceOfProbabilisticWinnerInDeterministicGame
        probabillisticGameDefinition
        performanceOfDeterministicWinnerInProbabillisticGame
        performanceOfProbabilisticWinnerInProbabillisticGame
        multigameDefinition
        multiGameOrAndAndDefinition

        subsubsection "Distinction problems" $ do
            deterministicDistinctionProblemDefinition
            deterministicDistinguisherDefinition
            probabillisticDistinctionProblemDefinition
            probabillisticDistinguisherDefinition
            distinguisherAdvantageDefinition
            -- distinctionGameDefinition
            bestDistinguisherAdvantage
            distinctionAdvantagePseudoMetric
            distinctionAdvantageRandomVariables
            splittingDistinctionProblem

        subsubsection "Bit guessing problems" $ do
            bitGuessingProblemDefinition
            bitGuesserDefinition
            bitGuesserAdvantageDefinition
            -- bitGuessingGameDefinition
            distinctionBitGuessingEquivalenceLemma
            bitGuessingPerformanceAmplification

        subsubsection "Search problems" $ do
            searchProblemDefinition
            searchProblemSolverDefinition
            -- searchProblemGameDefinition
            searchProblemSolverRepetition
            functionInversionDefinition
            oneWayFunctionDefinition

        subsubsection "Discrete games" $ do
            discreteGameDefinition


    subsection "Discrete Logarithms" $ do
        discreteLogarithmProblemDefinition
        additiveDLEasy
        dlReducable
        dlModTwoInEvenOrderGroup
        dlModTwoToTheKInDivGroup
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
    ma $ fa (sl ∈ solvs_) (a ⊆: perf_ sl)

informationTheoreticalHardness :: Note
informationTheoreticalHardness = do
    de $ do
        s ["Let", m probl_, "be a", searchProblem, and, m solvs_, "a", set, "of", solvers, for, m probl_]
        let po = partord_
        s ["Let", m perfs_, "be the", set, performanceValues, "associated with", m probl_, "such that", m perfs_, "is equipped with a", partialOrder, m po]
        let sl = "s"
            e = epsilon
        s ["If every", solver, m sl, "has a", performance, "smaller than some", m e <> ", we call", m probl_, "information-theoreticall", or, "unconditionally", eHard' e]
        ma $ fa (sl ∈ solvs_) (perf_ sl ⊆: e)
    nte $ do
        s ["A statement like this is often called information-theoretic or unconditional hardness because it holds for any solver, independently of its complexity"]

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
    let pp = mathcal "P"
        p = "P"
        q = "Q"
        d = ("D" !:)
        dp = d p
        dq = d q
        oo = perfs ""
    s ["Let", m pp, "be a set of", problems]
    s ["Let", m p, and, m q, "be the", weightedAverageCaseProblems, over, m dp, and, m dq, "respectively"]
    s ["Let their", performances, "be", m $ oo ⊆ reals]
    -- s ["Let", m p, and, m q, "be two", weightedAverageCaseProblems, with, probabilityDistributions, m dp, and, m dq, respectively, "with the same", set, "of", performances, m $ oo ⊆ reals]
    let o = "o"
        o1 = o !: 1
        o2 = o !: 2
        sl = "s"
    ma $ fa sl $ perf p sl <= perf q sl + (pars $ max (cs [o1, o2] ∈ oo) (abs $ o1 - o2)) * statd p q

    proof $ do
        let a = "a"
            b = "b"
        s ["Let", m $ ccint a b, "be any interval that is a superset of", m oo]
        ma $ oo ⊆ ccint a b
        s ["We will prove this by showing that the following inequality holds, which implies the theorem, because", m $ b - a >= (pars $ max (cs [o1, o2] ∈ oo) (abs $ o1 - o2)), "holds"]
        ma $ perf p sl - perf q sl <= (pars $ b - a) * statd p q
        s ["Consider the following two", sets, "of", problem, "instances"]
        let pr = "p"
            ppl = pp ^ "+"
        ma $ ppl =: setcmpr (pr ∈ p) (perf p pr >= perf q pr)
        let pmn = pp ^ "-"
        ma $ pmn =: setcmpr (pr ∈ q) (perf p pr <  perf q pr)
        s ["Note that", m ppl, and, m pmn, "form a", partition, "of", m pp]
        s ["Therefore, we note the following first"]
        aligneqs
            ( sumcmp (pr ∈ ppl) (pars $ prob (p =: pr) - prob (q =: pr))
            + sumcmp (pr ∈ pmn) (pars $ prob (p =: pr) - prob (q =: pr))
            )
            [ sumcmp (pr ∈ pp) (pars $ prob (p =: pr) - prob (q =: pr))
            , sumcmp (pr ∈ pp) (prob (p =: pr))
            - sumcmp (pr ∈ pp) (prob (q =: pr))
            , 1 - 1
            , 0
            ]
        s ["This is equivalent with the following equation"]
        ma $ sumcmp (pr ∈ ppl) (pars $ prob (p =: pr) - prob (q =: pr)) =: - sumcmp (pr ∈ pmn) (pars $ prob (p =: pr) - prob (q =: pr))
        s ["We now write the", statisticalDistance, "between", m p, and, m q, "in terms of that equation"]
        aligneqs
            (statd p q)
            [ (1 / 2) * sumcmp (pr ∈ pp) (abs $ prob (p =: pr) - prob (q =: pr))
            , (1 / 2) * (pars $
                sumcmp (pr ∈ ppl) (abs $ prob (p =: pr) - prob (q =: pr))
              + sumcmp (pr ∈ pmn) (abs $ prob (p =: pr) - prob (q =: pr)))
            , (1 / 2) * (pars $
                sumcmp (pr ∈ ppl) (prob (p =: pr) - prob (q =: pr))
              - sumcmp (pr ∈ pmn) (prob (p =: pr) - prob (q =: pr)))
            , (1 / 2) * (pars $
                sumcmp (pr ∈ ppl) (prob (p =: pr) - prob (q =: pr))
              + sumcmp (pr ∈ ppl) (prob (p =: pr) - prob (q =: pr)))
            , sumcmp (pr ∈ ppl) (pars $ prob (p =: pr) - prob (q =: pr))
            ]
        s ["Now we use this formula for the statistical distance to finally prove the inequality stated above"]
        aligneqs
            (perf p sl - perf q sl)
            [ sumcmp (pr ∈ pp) (prob (p =: pr) * perf pr sl)
            - sumcmp (pr ∈ pp) (prob (q =: pr) * perf pr sl)
            , sumcmp (pr ∈ pp) (pars $ prob (p =: pr) * perf pr sl - prob (q =: pr) * perf pr sl)
            , sumcmp (pr ∈ pp) ((pars $ prob (p =: pr) - prob (q =: pr)) * perf pr sl)
            , sumcmp (pr ∈ ppl) ((pars $ prob (p =: pr) - prob (q =: pr)) * perf pr sl)
            + sumcmp (pr ∈ pmn) ((pars $ prob (p =: pr) - prob (q =: pr)) * perf pr sl)
            ]
        s ["Now we use that", m $ perf pr sl, "is less than, or equal to", m b, "and that", m $ perf pr sl, "is greater than, or equal to,", m a]
        ma $ "" <= b * sumcmp (pr ∈ ppl) (pars $ prob (p =: pr) - prob (q =: pr))
                 + a * sumcmp (pr ∈ pmn) (pars $ prob (p =: pr) - prob (q =: pr))
        s ["We finish by noting that the second factor of the first term in the rigth-hand side of this inequality, is the", statisticalDistance, "between", m p, and, m q, "while the second factor of the second term is the exact opposite of that"]
        ma $ "" =: b * statd p q - a * statd p q =: (pars $ b - a) * statd p q









reductionDefinition :: Note
reductionDefinition = do
    let p = "p"
        q = "q"
    de $ do
        lab reductionDefinitionLabel
        lab reductionFunctionDefinitionLabel
        lab performanceTranslationFunctionDefinitionLabel
        s ["A", reduction', from, m q, to, m p]
        newline
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
    nte $ do
        s ["That", m tau, "needs to be", monotonic, "entails that a better", solver, for, m p, "won't make for a worse", solver, for, m q]
    de $ do
        lab reducibleDefinitionLabel
        s ["A", problem, m p, "is said to be", reducible, "to another", problem, m q, "if there exists a", reduction, "of", m p, to, m q]

reductionReeinterpretation :: Note
reductionReeinterpretation = thm $ do
    let p = "p"
        q = "q"
    let t_ = tau
        t = fn t_
        r_ = rho
        r = fn r_
        sl = "s"
    s ["A", tReduction t_, m r_, "of a", problem, m p, "to a", problem, m q, "can equivalently be interpreted as follows"]
    newline
    let l_ = lambda
        l = fn l_
    s ["Let", m $ fun l_ (perfs q) (perfs p), "be a", monotone, function, "satisfying the following inequality"]
    let (⊆:) = inposet $ partord_ !: p
    let a = "a"
    ma $ fa (a ∈ perfs p) $ a ⊆: l (t (a))
    s [the, reduction, "inequality can then be rephrased as follows"]
    ma $ fa (sl ∈ solvs p) $ perf p sl ⊆: l (perf q (r sl))

    proof $ do

        let (<<) = inposet $ partord_ !: q
        ma $ centeredBelowEachOther
            [ fa (sl ∈ solvs p) $ t (perf p sl) << perf q (r sl)
            , fa (sl ∈ solvs p) $ l (t (perf p sl)) ⊆: l (perf q (r sl))
            , fa (sl ∈ solvs p) $ perf p sl ⊆: l (perf q (r sl))
            ]



compositionOfReductions :: Note
compositionOfReductions = thm $ do
    lab compositionOfReductionsTheoremLabel
    textbf $ s [the, composition, "of", reductions]
    newline
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
    todo "Proof with inequality from the reinterpretation"


deterministicGameDefinition :: Note
deterministicGameDefinition = do
    de $ do
        lab deterministicGameDefinitionLabel
        lab gameDefinitionLabel
        lab playerDefinitionLabel
        let g = gme_
            w = plr_
            win_ = omega !: g
            win = fn win_
        let dd = mathcal "W"
        s ["A", deterministicGame', m g, or, gameInstance', "is an abstract object such that there exits a", set, m dd, "of so-called", cso [players', winners'], for, m g, "and a", function, m win_, "called the", winningCondition', "as follows"]
        ma $ fun win_ dd bits
        s ["If, for a given", player, m w <> ",", m $ win w, equals, m 1 <> ", we say that", m w, "wins the", game, m g]
        newline
        let gg = mathcal "G"
        s ["For a given", set, m gg, "of", games, anda, set, m dd, "of", solvers, "for all the", games, "in", m gg <> ", we define the", winningCondition', "in terms of all these", games, "as follows"]
        let wins_ = omega
            wins = fn2 wins_
        ma $ func2 wins_ gg dd bits g w (wins g w =: win w)


performanceOfDeterministicWinnerInDeterministicGame :: Note
performanceOfDeterministicWinnerInDeterministicGame = de $ do
    let g = gme_
        w = plr_
    let dd = mathcal "W"
    s [the, performanceFunction', "of a", deterministicGame', m g, "is defined by viewing its", players, "as solvers"]
    s [the, set, "of", performanceValues, "is", m bits, "and the", performanceFunction, "is defined by whether a", player, "wins the", deterministicGame]
    let win_ = omega !: g
        win = fn win_
    ma $ func (perff g) dd bits w $ win w

probabillisticWinnerDefinition :: Note
probabillisticWinnerDefinition = de $ do
    let dd = mathcal "W"
        ww = "W"
    s ["A", probabilisticWinner', m $ prdis_ ww, "is a", probabilityDistribution, "of a", xRv dd]

performanceOfProbabilisticWinnerInDeterministicGame :: Note
performanceOfProbabilisticWinnerInDeterministicGame = de $ do
    let dd = mathcal "W"
    let g = gme_
        win_ = omega !: g
        win = fn win_
        ww = "W"
    s ["Let", m dd, "be a set of", deterministicWinners, "for a", deterministicGame, m g]
    s ["Let", m ww, "be a", probabilisticWinner, over, m dd <> ", then we define the", performanceFunction, with, performanceValues, "in", m $ ccint 0 1]
    ma $ func (perff g) (prdss ww) (ccint 0 1) (prdis_ ww) (perf g (prdis_ ww) =: prdis ww (win (ww) =: 1))

probabillisticGameDefinition :: Note
probabillisticGameDefinition = de $ do
    let gg = mathcal "G"
    s ["Let", m gg, "be a", set, "of", deterministicGames]
    let gr = "G"
    s ["A", probabilisticGame', m $ prdis_ gr, over, m gg, "is a", probabilityDistribution, "of a", randomVariable, m gr, over, m gg]

performanceOfDeterministicWinnerInProbabillisticGame :: Note
performanceOfDeterministicWinnerInProbabillisticGame = de $ do
    let w = plr_
    let gg = mathcal "G"
        gr = "G"
    let dd = mathcal "W"
    s ["Let", m gg, "be a", set, "of", games, and, m dd, "a", set, "of", solvers, "for all the", games, "in", m gg]
    s ["Let", m $ prdis_ gr, "be a", probabilisticGame, over, m gg <> ", then we define the", performanceFunction, with, performanceValues, "in", m $ ccint 0 1, for, deterministicWinners, m w, "as follows"]
    let wins_ = omega
        wins = fn2 wins_
    ma $ func (perff gr) dd (ccint 0 1) w $ prdis gr (wins gr w =: 1)

performanceOfProbabilisticWinnerInProbabillisticGame :: Note
performanceOfProbabilisticWinnerInProbabillisticGame = de $ do
    let gg = mathcal "G"
        gr = "G"
    let dd = mathcal "W"
        ww = "W"
    let wins_ = omega
        wins = fn2 wins_
    s ["Let", m gg, "be a", set, "of", games, and, m dd, "a", set, "of", solvers, "for all the", games, "in", m gg]
    s ["Let", m $ prdis_ gr, "be a", probabilisticGame, over, m gg <> ", then we define the", performanceFunction, with, performanceValues, "in", m $ ccint 0 1, for, probabilisticWinners, m $ prdis_ ww, over, m dd, "as follows"]
    ma $ func (perff gr) (prdss ww) (ccint 0 1) (prdis_ ww) $ perf gr (prdis_ ww) =: prdiss [ww, gr] (wins gr ww =: 1)


multigameDefinition :: Note
multigameDefinition = de $ do
    let g = gme_
        w = plr_
    let gg = mathcal "G"
    let dd = mathcal "W"
    s ["Let", m gg, "be a", set, "of", games, and, m dd, "a", set, "of", solvers, "for all the", games, "in", m gg]
    let i = "i"
        wins_ i = omega !: i
        wins i = fn2 $ wins_ i
    s ["Consider the scenario in which there are multiple", winningConditions, m $ wins_ i]
    ma $ fun2 (wins_ i) gg dd bits
    s [m $ wins i g w, "is interpreted as", dquoted $ s [m w, "wins the", m i <> "-th", subgame', "of", m g]]
    s ["We then call this a", multiGame']
    todo "That's really vague, is there really no better way to state this?"

multiGameOrAndAndDefinition :: Note
multiGameOrAndAndDefinition = de $ do
    let g = gme_
        w = plr_
        k = "k"
    s ["Let", m g, "be a", multiGame, with, m k, subgames]
    s ["We denote by", m $ orgame g, and, m $ andgame g, "the logical or and the logical and, respectively, of the", m k, "subgames"]
    let i = "i"
    ma $ wins (orgame g) w =: orcompr (i =: 1) k (winsub i g w)
    ma $ wins (andgame g) w =: andcompr (i =: 1) k (winsub i g w)

deterministicDistinctionProblemDefinition :: Note
deterministicDistinctionProblemDefinition = de $ do
    lab distinctionProblemDefinitionLabel
    lab distinguisherDefinitionLabel
    s ["Let", m objs_, "be an abstract set of objects"]
    s ["A", deterministicDistinctionProblem', "is the", problem, "of distinguishing between two fixed objects from a set", m objs_]
    let o = "o"
        o1 = o !: 0
        o2 = o !: 1
        p = dprob o1 o2
    s ["A", deterministicDistinctionProblem, "consists of a pair", m $ tuple o1 o2, "of objects from", m objs_, "and is denoted as", m p]
    -- let ss = "S"
    --     s0 = ss !: 0
    --     s1 = ss !: 1
    --     p = dprob s0 s1
    -- s ["An abstract", distinctionProblem', "is a pair of", nSs 1, m $ tuple s0 s1, "and is denoted as", m p]

deterministicDistinguisherDefinition :: Note
deterministicDistinguisherDefinition = do
    de $ do
        lab distinguisherDefinitionLabel
        let o = "o"
            o0 = o !: 0
            o1 = o !: 1
            p = dprob o0 o1
        s ["Let", m p, "be a", distinctionProblem]
        let ds = mathcal "D"
        s ["A", solver, "which, in this case, is called", distinguisher', "is supposed to guess which of the two objects it is given access to"]
        s ["Let", m ds, "be a", set, "of such abstract", distinguishers]
        let d = "d"
            o = "o"
        s ["A", function, m guess_, "as follows determines the guess of a given", distinguisher, m d, "when given access to a given object", m o]
        ma $ fun2 guess_ ds objs_ bits
        let i = "i"
        s [m $ guess d o =: i, "is interpreted as", dquoted $ s [m d, "guesses that it sees", m $ o !: i, "when given", m o]]
        -- let ss = "S"
        --     s0 = ss !: 0
        --     s1 = ss !: 1
        --     p = dprob s0 s1
        -- s ["A", distinguisher', "for a", distinctionProblem, m p, "is a", nS 2, "which at one", interface, "connects to a", system, m ss, "(either", m s0, or, m s1 <> ")", "and at the other", interface, "outputs a bit"]
    -- nte $ do
        -- s ["A", distinguisher, "can be both deterministic or probabilistic and is therefore usually assumed to be probabilistic"]

probabillisticDistinctionProblemDefinition :: Note
probabillisticDistinctionProblemDefinition = de $ do
    s ["Let", m objs_, "be a set of objects"]
    let o = "O"
        o0 = o !: 0
        o1 = o !: 1
        p = dprob o0 o1
    s ["If", m o0, and, m o1, are, xRvs objs_, "then we call", m p, "a", probabilisticDistinctionProblem']


probabillisticDistinguisherDefinition :: Note
probabillisticDistinguisherDefinition = de $ do
    let o = "o"
        o0 = o !: 0
        o1 = o !: 1
        p = dprob o0 o1
    let ds = mathcal "D"
    s ["let", m p, "be a", distinctionProblem, and, m ds, "a", set, "of", deterministicDistinguishers]
    s ["A", probabilisticDistinguisher', "is a", xRv ds]

distinguisherAdvantageDefinition :: Note
distinguisherAdvantageDefinition = de $ do
    let o = "o"
        o0 = o !: 0
        o1 = o !: 1
        p = dprob o0 o1
        d = "d"
    s ["Let", m p, "be a", deterministicDistinctionProblem, and, m d, "a", deterministicDistinguisher]
    s ["We define the", advantage', m $ dadv d o0 o1, "of", m d, "as follows"]
    ma $ dadv d o0 o1 =: prob (guess d o1 =: 1) - prob (guess d o0 =: 1)
    let dd = "D"
    s ["If", m dd, "is a", probabilisticDistinguisher, "then we define the", advantage, "as follows"]
    ma $ dadv dd o0 o1 =: prob (guess dd o1 =: 1) - prob (guess dd o0 =: 1)
    let oo = "O"
        oo0 = oo !: 0
        oo1 = oo !: 1
        pp = dprob oo0 oo1
    s ["If", m pp, "is a", probabilisticDistinctionProblem, "then we define the", advantage, "as follows"]
    ma $ dadv d oo0 oo1 =: prob (guess d oo1 =: 1) - prob (guess d oo0 =: 1)
    s [the, advantage, "of a", probabilisticDistinguisher, m dd, "in a", probabilisticDistinctionProblem, m pp, "is defined as follows"]
    ma $ dadv dd oo0 oo1 =: prob (guess dd oo1 =: 1) - prob (guess dd oo0 =: 1)
    todo "Rewrite these in function definition (with sets) notation"

    -- let ss = "S"
    --     s0 = ss !: 0
    --     s1 = ss !: 1
    --     d = "D"
    -- de $ do
    --     let p = dprob s0 s1
    --         ad = dadv d s0 s1
    --     s [the, advantage', m ad, "of a", distinguisher, m d, "for a", distinctionProblem, m p, "in distinguishing", m s0, and, m s1, "is defined as follows"]
    --     ma $ ad =: prob (conv_ d s1 =: 1) - prob (conv_ d s0 =: 1)
    -- nte $ do
    --     s ["Note that", m $ prob (conv_ d s1 =: 1), and, m $ prob (conv_ d s0 =: 1), "are probabilities in different random experiments"]
    --     s ["In one experiment the", distinguisher, "is guessing the identity of", m s0, and, "in the other it's guessing the identity of", m s1]
    -- de $ do
    --     let dd = mathcal "D"
    --     s ["We define the", advantage, "of a", set, m dd, "of", distinguishers, "as the", supremum, "of all the individual", distinguishers]
    --     ma $ dadv dd s0 s1 =: supcomp (d ∈ dd) (dadv d s0 s1)
    --     s ["Moreover, we denote the", advantage, "of the", set, "of all possible", distinguishers, "as", m $ dadvs s0 s1]

-- distinctionGameDefinition :: Note
-- distinctionGameDefinition = de $ do
--     lab distinctionGameDefinitionLabel
--     let ss = "S"
--         s0 = ss !: 0
--         s1 = ss !: 1
--         p = dprob s0 s1
--     s ["A", deterministicDistinctionGame', "for a", distinctionProblem, m p, "(deterministically) outputs either", m s0, or, m s1, "at one", interface, "and receives a bit at that same", interface]
--     s ["It then outputs a set bit if the bit that it receives matches the index of the", system, "it outputted before"]
--     newline
--     s ["A (probabilistic)", distinctionGame', "for a", distinctionProblem, m p, "is a", randomVariable, "over the", deterministicDistinctionGames, "for", m p]
--
--     s ["A", solver, "for a", distinctionGame, "for a", distinctionProblem, m p, "is a", distinguisher, "for", m p]
--     s [the, performanceValues, "of such a", solver, "lie in the interval", m $ ccint (-1) 1]
--     newline
--     s [the, performanceFunction, "is then defined as mapping a", distinguisher, "to its", advantage]

bestDistinguisherAdvantage :: Note
bestDistinguisherAdvantage = de $ do
    let oo = "O"
        oo0 = oo !: 0
        oo1 = oo !: 1
        pp = dprob oo0 oo1
    let ds = mathcal "D"
    s ["Let", m ds, "be a", set, "of", distinguishers, "for a", distinctionProblem, m pp]
    s [the, advantage, "of the best", distinguisher, "is defined as follows"]
    let d = "D"
    ma $ dadv ds oo0 oo1 =: supcomp (d ∈ ds) (dadv d oo0 oo1)
    s ["We use", m $ dadvs oo0 oo1, "to mean the", advantage, "of the best", distinguisher, "out of all possible", distinguishers]
    todo "probabilistic distinguishers are not better than deterministic ones"

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
    s ["Let", m x, and, m y, "be two", xRvs reals]
    s [the, advantage, "of the best", distinguisher, "for", m $ dprob x y, "is the", statisticalDistance, m $ statd x y]
    ma $ dadvs x y =: statd x y
    toprove
    todo "Does there really exist such a distinguisher or it just an upper bound?"

splittingDistinctionProblem :: Note
splittingDistinctionProblem = lem $ do
    let o = "O"
        k = "k"
        i = "i"
        (o1, o2, ok, os) = buildList o k
        oo = mathcal "O"
    s ["Let", m os, "be objects in (or", randomVariables, "over) a", set, m oo]
    s [m $ dprob o1 ok, "can be reduced to the combination of the problems", m $ dprob (o !: i) (o !: (i + 1))]
    s ["Then we find the following"]
    let d = "D"
    ma $ fa d $ dadv d o1 ok =: dadv d o1 o2 + dadv d o2 (o !: 3) + dotsb + dadv d (o !: (k - 1)) ok
    toprove


bitGuessingProblemDefinition :: Note
bitGuessingProblemDefinition = de $ do
    lab bitGuessingProblemDefinitionLabel
    s ["A", bitGuessingProblem', "is the abstract problem of guessing a hidden bit from a given object"]
    let o = "o"
        oo = mathcal "O"
        z = "z"
    s ["Concretely: Let", m o, "be an objects from a", set, m oo, "of objects", and, m $ z ∈ bits, "a bit"]
    s [m $ bgprob o z, "is then the problem of guessing", m z, from, m o]
    todo "Split into deterministic and probabilistic"

bitGuesserDefinition :: Note
bitGuesserDefinition = de $ do
    lab bitGuesserDefinitionLabel
    let ds = "D"
        oo = mathcal "O"
    s ["Let", m ds, "be a", set, "of so-called", bitGuessers, "for a", bitGuessingProblem, "for the objects in", m oo]
    s ["A", bitGuesser', "is an abstract object in", m ds, "such that there exists a so-called guessing-function", m guess_, "as follows"]
    ma $ fun2 guess_ ds oo bits
    let d = "d"
        o = "o"
        z = "z"
    s [m $ guess d o =: z, "can be interpreted as the statement that", m d, "guesses the bit", m z, "upon receiving object", m o]

bitGuesserAdvantageDefinition :: Note
bitGuesserAdvantageDefinition = de $ do
    let gg = "G"
        oo = "O"
        zz = "Z"
    s [the, advantage, "of a", bitGuesser, m gg, advantage', "in a", bitGuessingProblem, m $ bgprob oo zz, "is defined as follows"]
    ma $ gadv gg =: 2 * (pars $ prob (guess gg oo =: zz) - (1 / 2))
    s ["The value of the", advantage, "lies in the interval", m $ ccint (-1) 1]

-- bitGuessingGameDefinition :: Note
-- bitGuessingGameDefinition = de $ do
--     let b = "B"
--     s ["A", deterministicBitGuessingGame', "for a", bitGuessingGame, m b, "(deterministically) has", m b, "output its bit and receives a bit at its inside interface from a", player]
--     s ["It then outputs a set bit (win) if the two bits equal"]
--     newline
--     s ["A (probabilistic)", bitGuessingGame', "for a", bitGuessingProblem, m b, "is", game, "is a", randomVariable, "over the deterministic", bitGuessingGames, for, m b]
--     s ["A", solver, "for a", bitGuessingGame, "for a", bitGuessingProblem, m b, "is a", bitGuesser, for, m b]
--     s [the, performanceValues, "of such a", solver, "lie in the interval", m $ ccint (-1) 1]
--     s [the, performanceFunction, "is then defined as mapping a", bitGuesser, "to its", advantage]

distinctionBitGuessingEquivalenceLemma :: Note
distinctionBitGuessingEquivalenceLemma = lem $ do
    s [distinctionProblems, "can be regarded as a special case of", bitGuessingProblems, "where the bit is uniform"]
    proof $ do
        let d = "D"
            b = "B"
        s ["We prove this by showing that for any", distinctionProblem, m d, "there exists a", bitGuessingProblem, m b, "such that every", distinguisher, "for", m d, "can be used to construct a", bitGuesser, for, m b, "with the same (or better)", advantage]
        toprove

bitGuessingPerformanceAmplification :: Note
bitGuessingPerformanceAmplification = thm $ do
    let pp = mathcal "P"
        p = spwc pp
    s ["Let", m pp, "be a", set, "of", bitGuessingProblems, and, "let", m p, "be their", worstCaseProblem]
    let sl = "S"
        e = epsilon
    s ["Let", m sl, "be a", solver, with, performance, m e, on, m p]
    ma $ perf p sl =: e
    let st = "T"
        q = "n"
    s ["Let", m $ nat q, "be an", odd, naturalNumber, "and let", m st, "be the", solver, "that invokes", m sl, "exactly", m q, "times (each time which fresh and independent randomness) and then outputs the majority-voted bit"]
    let d = delta
    s ["Let", m $ d ∈ ooint 0 1, "be a real number"]
    let qb = 2 / e ^ 2 * ln (2 / delta)
    s ["For", m st, "to have a", performance, "greater than, or equal to", m (1 - delta) <> ", it needs to call", m sl, "at least", m qb, "times"]
    ma $ q >= qb ⇒ perf p st >= (1 - delta)

    proof $ do
        let x = "X"
            i = "i"
            (_, _, _, xi, xs) = buildiList x q i
        let p = "p"
        s ["Let", m xs, "be the", xRvs bits, "that represent whether the bit that", m sl, "outputs was correct in each of", m q, "rounds"]
        s ["Because", m sl, "has", performance, m e, "we find the following"]
        ma $ p =: prob (xi =: 1) =: (1 / 2) + (e / 2)
        s ["Now note that all", m xi, are, independent, "and that", m st, "outputs the wrong bit if and only if", m sl, "outputs more wrong bits than correct bits"]
        s ["This that", m st, "outputs the wrong bit with the following", probability]
        ma $ prob (sumcmpr (i =: 1) q xi < (q / 2))
        let a = alpha
        s ["Define", m a, "as", m $ (e / 2) =: p - (1 / 2), "such that", m $ (pars $ p - a) * q =: (q / 2), holds]
        s ["We now use", hoeffdingsInequality, ref hoeffdingsInequalityTheoremLabel, "to obtain the following bound in this probability"]
        ma $ prob (sumcmpr (i =: 1) q xi < (pars $ p - a) * q) <= exp (-2 * a ^ 2 * q)
            =: exp (- (q * e ^ 2) / 2)
        s ["Let", m q, "now be greater than, or equal to", m qb, "and use that the exponential function is", monotonic]
        refneeded "proof that exp is monotonic"
        ma $ exp (- (q * e ^ 2) / 2)
            <= exp (- ((2 / e ^ 2 * ln (2 / delta)) * e ^ 2) / 2)
            =: exp (- ((2 * ln (2 / delta))) / 2)
            =: exp (- (ln (2 / delta)))
            =: 1 / (2 / delta)
            =: (delta / 2)
        s ["Hence the success probability of", m st, "is at least", m $ 1 - delta / 2, "and the", performance, "of", m st, "is at least", m $ 1 - delta]


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
        s ["A", probabilisticSearchProblemSolver', "is a", randomVariable, "over all the", deterministicSearchProblemSolvers, "for the same", searchProblem]
    nte $ do
        s ["The output of a", probabilisticSearchProblemSolver, "for a given instance is a", randomVariable, "over the", witnessSpace, m wsp_]

-- searchProblemGameDefinition :: Note
-- searchProblemGameDefinition = de $ do
--     lab searchProblemGameDefinitionLabel
--     s ["Let", m $ probl_ =: sprob_, "be a", searchProblem]
--     let x = "x"
--         w = "w"
--     s ["A", deterministicSearchProblemGame, for, m probl_, anda, "given instance", m x, "(deterministically) outputs", m x, "at its inside", interface, "and receives a", witness, m w, "at that same", interface]
--     s ["It then outputs a set bit (win) if", m $ sol x w, "holds"]
--     s ["For a", deterministicSearchProblemGame, "the", performanceValues, "are", m bits]
--     newline
--     let g = "G"
--     s ["A", probabillisticSearchProblemGame, m g, for, m probl_, "is a", randomVariable, "over the", deterministicSearchProblemGames, for, m probl_]
--     let sl = "S"
--     s ["A solver is then a", probabilisticSearchProblemSolver, m sl]
--     s [the, performanceValues, "lie in the interval", m $ ccint 0 1, "and the", performanceFunction, "is defined as follows"]
--     let xx = "X"
--     ma $ perf g sl =: prob (sol xx (fn sl xx))
--     s ["Here", m xx, "is the", randomVariable, "corresponding to the input to the", searchProblemSolver]
--     s ["In other words, the", performance, "of a", searchProblemSolver, "is the", probability, "that it finds a valid", witness]
--
--     todo "define advantage independently of game, just for a solver?"

searchProblemSolverRepetition :: Note
searchProblemSolverRepetition = thm $ do
    s ["Simply repeatedly applying the same", probabilisticSearchProblemSolver, "to a given instance of a", searchProblem, "does not necessarily boost the success", probability]
    newline
    let sl = "S"
        sl' = "S'"
        a = alpha
    s ["More formally, let", m sl, "be a", probabilisticSearchProblemSolver, "for a", searchProblem, m sprob_, with, successProbability, m $ a ∈ ocint 0 1, "such that", m spred_, "can be efficiently computed"]
    s ["Let", m sl', "be a", probabilisticSearchProblemSolver, "defined as follows"]
    let x = "x"
        w = "w"
    s ["Given an instance", m $ x ∈ isp_, "it first invokes", m sl, "on input", m x, "to obtain", m w]
    s ["If", m $ sol x w, "holds then", m sl', "returns", m w]
    let w' = "w'"
    s ["Otherwise it invokes", m sl, "again on input", m x, "to obtain", m w', "and returns", m w']
    s ["The best lower bound on the", successProbability, "is", m a]

    proof $ do
        s ["It is easy to see that", m sl', "has", successProbability, "at least", m a]
        s ["Now it suffices to show that there exists a", searchProblem, m sprob_, anda, probabilisticSearchProblemSolver, m sl, "such that", m sl', "has", successProbability, m a, for]
        let x0 = x !: 0
            x1 = x !: 1
        s ["Consider a", searchProblem, "with only two possible instances", m $ wsp_ =: setofs [x0, x1]]
        s ["Let", m sl, "be a", solver, "that finds a valid", witness, "given", m x0, "with probability", m a, "but never finds a valid", witness, "given", m x1]
        s [the, successProbability, "of", m sl, is, m a <> ",but the", successProbability, "of", m sl', "is also", m a]


dlNotation :: Note
dlNotation = de $ do
    s ["We use", m $ dlp dlgrp_, "to denote the", discreteLogarithm, searchProblem, "in the", group, m dlgrp_]

lsbProbNotation :: Note
lsbProbNotation = de $ do
    let x = "x"
        y = "y"
    s ["We use", m $ lsbp dlgrp_, "to denote the", searchProblem, "of finding the", leastSignificantBit, m $ x `mod` 2, "of the", discreteLogarithm, m x, "of a", group, element, m y, "in the", group, m dlgrp_, "chosen uniformly at random"]

dlLSBHardness :: Note
dlLSBHardness = do
    thm $ do
        let h = "h"
        let grps_ = "H"
            grp_ = grp "H" grpop_
            o = "m"
        s ["Let", m $ grp_ =: grp (genby h) grpop_, "be a", finite, cyclic, group, "generated by", m $ h ∈ grps_, "of", odd, order, m o]
        let d = delta
            e = epsilon
            sol = "S"
            lp = lsbp grp_
            lpa = spac lp
            lpw = spwc lp
            dp = dlpw grp_
            q = "Q"
        center $ s [m dp, is, reducible, to, m lpa]
        s ["More formally: For any", m $ cs [d, e] ∈ ccint 0 1, "and for any", solver, m sol, for, m lpa, with, performance, "greater than", m e <> ",", "there exists a solver", m q, "for", m dp, with, performance, "at least", m $ 1 - d, "which invokes", m sol, "a polynomial number of times (with respect to", csa [m $ log (1 / d), m $ 1 / e, m $ log o] <> ")", "and otherwise performs only a few simple operations"]
        newline
        newline
        s ["In other words: If, for some", m (d < 1) <> ", there exists no polynomial-time algorithm for solving", m dp, with, performance, "at least", m (1 - d) <> ", then there exists no algorithm for solving", m lpa, "with non-negligible", performance]

        proof $ do
            s ["We prove this via a", reduction, from, m dp, to, m lpa]
            s ["In fact, we will use multiple", reductions]
            s ["The composition of these", reductions, "will complete the reduction from", m dp, to, m lpa, ref compositionOfReductionsTheoremLabel]
            newline
            let n = "n"
            s ["Let", m n, "be a fixed", integer, "parameter"]
            s ["We divide the", integer, "interval", m $ ccint 0 (o - 1), "into segments of length", m $ roundu (o / n), "( where the last segment can be shorter)"]
            let i = "I"
            s ["Let", m i, "be the interval of", elements, "generated by powers of", m h, "that are in the first segment"]
            let i_ = setlist (h ^ 0) (h ^ 1) (h ^ (roundu (o / n) - 1))
            ma $ i =: i_ ⊆ grps_
            let t = "t"
            s ["Let", m t, "be the number of bits necessary to represent the", discreteLogarithm, "of an", element, "of", m i]
            ma $ (t =:) $ roundu $ logn 2 $ (roundd $ o / n) + 1

            let p = "p"
            s ["Define", m (p `restrictedTo` i), "as the problem", m p, "where the", instanceSpace, "is restricted to", m i]
            s ["We complete the proof with the following five reductions"]
            let reduced = "reduced"
            let dpi = dp `restrictedTo` i
            let liw = lpw `restrictedTo` i
            let j_ = "J"
                j = fn j_
                x = "x"
            let lsbjx = lpa `restrictedTo` (j x)
            let a = alpha
                (<-.) = binop $ comm0 "mapsfrom"
            hereFigure $ linedTable
                ["from", "to", "performance", "calls"]
                [ [dp   , dpi  , a <-. a                            , n ]
                , [dpi  , liw  , ("" >= 1 - 2 * t * a) <-. (1 - a)  , t ]
                , [liw  , liw  , "TODO"                             , "TODO"]
                , [liw  , lsbjx, "TODO"                             , "TODO"]
                , [lsbjx, lpa  , "TODO"                             , "TODO"]
                ]

            s ["We construct each", reduction, "separately as follows"]
            enumerate $ do
                item $ do
                    s ["In the first", reduction, m dp, is, reduced, to, m dpi]
                    newline
                    let sl = "S"
                        si = sl !: i
                        sh = sl !: grps_
                    s ["Let", m si, "be a", solver, for, m dpi, with, performance, m a]
                    s ["We construct a", solver, m sh, for, m dp, "as follows"]
                    newline
                    let x = "x"
                        y = "y"
                    s ["Let", m $ y =: h ^ x, "be a query where", m $ y ∈ i, "holds"]
                    let l = "l"
                        y' = ((y <> "'") .!:)
                    s ["For each", m l, "in", m (setlist 0 1 (n - 1)) <> ",", m sh, "first computes", m $ y' l, "as follows"]
                    ma $ y' l =: y ** h ^ (- l * roundu (o / n)) =: h ^ (x - l * roundu (o / n))
                    let x' = ((x <> "'") .!:)
                    s [m sh, "then invokes", m sl, on, m $ y' l, "to obtain", m $ x' l]
                    s ["Note that for one of the values of", m l <> ",", m $ y' l, "will be in", m i]
                    s [m sh, "checkes that", m $ x' l, "is a correct solution by checking the following equation"]
                    ma $ y' l =: h ^ (x' l)
                    s ["If", m $ x' l, "is a valid solution, then the solution for the query", m y, "is calculated as follows"]
                    ma $ x =: x' l + l * roundu (o / n)
                    s ["This means that", m sh, "needs to invoke", m si, "at most", m n, "times and has", performance, m a]
                item $ do
                    s ["In the second", reduction, m dpi, is, reduced, to, m liw]
                    let sl = "S"
                        sli = sl !: "L"
                        sdi = sl !: "D"
                    newline
                    s ["Let", m sli, "be a", solver, for, m liw, with, performance, m $ 1 - alpha]
                    s ["We construct a", solver, m sdi, for, m dpi, "as follows"]
                    newline
                    let x = "x"
                        y = "y"
                    s ["Let", m $ y =: h ^ x, "be a query"]
                    let b = "b"
                    s [m sdi, "determines (guess for) the", leastSignificantBit, m b, "of", m x, "by invoking", m sli]
                    s [m sdi, "does check whether (or do anything different if)", m b, "is incorrect"]
                    let y' = y <> "'"
                    s ["It then computes", m y', "as follows", ref finiteOddGroupRootComputationTheoremLabel]
                    ma $ (y' =:) $ cases $ do
                        y ** h ^ (-1) & text "if " <> m b =: 1
                        lnbk
                        y & text "otherwise"
                    let x' = x <> "'"
                    s ["Now the power", m x', "of", m h, "that", m y', "represents is", even]
                    let z = "z"
                    s ["Because", m o, is, odd, "we can compute the (unique)" <> ref squareRootUniqueInFiniteOddGroupTheoremLabel, squareRoot, m z, "of", m y', "as follows", ref finiteOddGroupRootComputationTheoremLabel]
                    ma $ z =: y' ^ ((o + 1) / 2) =: h ^ (x' / 2) =: h ^ (roundd $ x / 2)
                    s ["We then repeat this process with", m z, "instead of", m y, "to compute the next", leastSignificantBit, "of", m x]
                    s ["After", m $ roundu $ logn 2 x, "invocations of", m sli <> ",", m sdi, "has computed all the bits of", m x, "and therefore", m x]
                    s ["Because", m y, "is in", m i <> ",", m x, "must be in", m $ setlist 0 1 (roundu (o / n) - 1), "and therefore", m $ roundu $ log2 x, "will be smaller than", m t]
                    clarify "How does it exactly compute x? make a reference, don't show it here."
                    s [the, performance, "of", m sdi, "is then at least", m $ 1 - 2 * t * a, ref unionBoundTheoremLabel]
                    why_ "exactly? union bound doesn't help as much as it should"

            toprove

    nte $ do
        s ["We assert that the", order, is, odd, "because otherwise guessing the LSB is easy", ref dLModTwoInEvenOrderGroupTheoremLabel]







discreteLogarithmProblemDefinition :: Note
discreteLogarithmProblemDefinition = do
    de $ do
        lab discreteLogarithmDefinitionLabel
        lab dLDefinitionLabel
        let aa = "A"
            a = "a"
            g = "g"
        s [the, discreteLogarithm', "(" <> dL' <> ")", searchProblem, "for a", cyclic_, group, m $ grp_ =: grp (genby g) grpop_, "is the problem of computing, for a given", group, element, m $ aa ∈ grps_, "the exponent", m $ int a, " such that", m $ aa =: g ^ a, "holds"]
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
        s ["Recall that, for any element", m (z ∈ intmod n) <> ", we are looking for the integer", m $ int a, "such that", m $ z =: g * a, "where", m g, "is a", generator, "of", m $ intagrp n]
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
        s ["There then exists a", m $ int c, "such that", m c, "is the", discreteLogarithm, "base", m g, "in", m grp_, "of", m z]
        ma $ z =: h ^ b =: g ^ c
        let d = "d"
        s ["Because", m h, "is an", element, "of", m grps_ <> ",", "there exists a", m $ int d, "such that", m $ h =: g ^ d, "holds"]
        ma $ z =: (pars $ g ^ d) ^ b =: g ^ c
        s ["This means that we have the following equation for", m c, "in", m $ intring $ ord grps_]
        ma $ d * b =: c
        s ["The algorithm now uses", m a, "to find", m c, from, m z, and, m d, from, m h]
        s ["It then computes the multiplicative inverse of", m d, "in", m $ intring $ ord grps_, "with the extended Euclidean algorithm and finally computes", m b, "by evaluating", m $ rinv d * c =: rinv d * d * b =: b]

dlModTwoInEvenOrderGroup :: Note
dlModTwoInEvenOrderGroup = thm $ do
    lab dLModTwoInEvenOrderGroupTheoremLabel
    let n = "n"
    s ["Let", m grp_, beA, group, with, "an", even, order, m $ ord grp_ =: 2 * n]
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

dlModTwoToTheKInDivGroup :: Note
dlModTwoToTheKInDivGroup = thm $ do
    let n = "n"
        k = "k"
    s ["Let", m grp_, beA, group, with, "an", order, m $ ord grp_ =: 2^k * n, "for some", m k]
    s ["There exists an efficient algorithm to compute the", discreteLogarithm, "of an", element, "modulo", m $ 2^k]

    toprove


dlRepetitionBoosting :: Note
dlRepetitionBoosting = do
    thm $ do
        let g = "g"
            grp_ = grp (genby g) grpop_
            q = "q"
        s ["Let", m grp_, "be a", cyclic, group, "of order", m q]
        let sl = "S"
            sl' = "S'"
            a = alpha
        s ["If there exists a", deterministicSearchProblemSolver, m sl, for, m $ dlp grp_, with, successProbability, m a <> ",", "then it can be used to build a", deterministicSearchProblemSolver, m sl', with, successProbability, "strictly greater than", m a]
        s ["That is", m sl, "outputs the same result for the same arguments, but a randomly chosen", element, "will yield a correct result with", probability, m a]

        proof $ do
            s ["For a given result, it can be checked whether that result is correct, but since", m sl, "is deterministic, that will not get us any farther as-is"]
            s ["The idea is to repeat the invocation of", m sl, on, elements, "of", m grps_, "that are different from, but related to the query in such a way that the would-be result for the original query can be derived from the results of the new elements"]
            newline
            let h = "h"
                x = "x"
                c = "c"
            s ["Let", m $ h =: g ^ x ∈ grps_, "be an input for", m sl', and, m $ nat c, "a constant"]
            s [m sl', "will operate as follows"]
            let r = "r"
            itemize $ do
                item $ do
                    s [m sl', "chooses", m $ r ∈ intmod q, "uniformly at random and invokes", m sl, "on", m $ h ** g ^ r =: g ^ (x + r)]
                let y = "y"
                    z = "z"
                item $ do
                    s [the, "output", m y, from, m sl, "is checked for correctness by checking that", m $ g ^ y, "equals", m $ h ** g ^ r]
                item $ do
                    s ["If the ouput from", m sl, "is correct for input", m $ h ** g ^ r, "then", m sl', "computes", m $ z =: y - r]
                    s ["This must then equal", m x, "so", m sl', "outputs it"]
                item $ do
                    s ["If the output from", m sl, "is not correct, it tries again with another randomly chosen", element, from, m $ intmod q, "for at most", m c, "times, after which it will just output the last gotten output from", m a]
            s ["Note that", m sl, "succeeds with", probability, m a, "because", m $ h ** g ^ r, "is a uniformly random element"]
            s ["Hence, the success", probability, "of", m sl', "is bigger than that of", m sl]
            ma $ 1 - (pars $ 1 - a) ^ c > a
    nte $ do
        s ["The crucial property of the above algorithm is that it invokes its subroutine each time on a uniformly random instance such that the output can be used to construct an output for the given query"]
        s ["In general the output for an other uniformly random instance cannot be transformed back to a solution to the original instance."]
        s ["Problems that allow this are called random self-reducible"]
        todo "Defined random self-reducible formally and separately"


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


discreteGameDefinition :: Note
discreteGameDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
    s ["A", deterministicDiscreteGame', or, dDS', "can be described as a", xyS xx yy, "in addition to outputing an", element, "of", m yy, "upon receival of an input", element, "of", m xx, "it also outputs a bit indicating whether the game has been won"]
    s ["The bit is monotone in the sense that it is initally set to", m 0 <> ", changes to", m 1, "once the game is won and never changes back"]
    s ["For", xyDS xx (yy ⨯ bits) <> ", the binary component of the output is called a", monotoneBinaryOutput', or, mBO']
    s ["Such a", deterministicDiscreteSystem, "with a", monotoneBinaryOutput, "is called an", xyDDG xx yy]

discreteGameWinnerDefinition :: Note
discreteGameWinnerDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
    s ["A", deterministicDiscreteWinner', or, dDW', yxDDW yy xx, "for a", xyDDG xx yy, "is a", yxDE yy xx]
    s ["A", dDW, "is generally understood not to receive the 'wins' bit"]








