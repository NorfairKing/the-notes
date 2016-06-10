module Cryptography.ComputationalProblems.Abstract where

import           Notes

import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Logic.FirstOrderLogic.Macro
import           Probability.Distributions.Macro
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Relations.Orders.Macro
import           Relations.Orders.Terms                            hiding
                                                                    (order)
import           Sets.Basics.Terms
import           Sets.Partition.Terms

import           Cryptography.ComputationalProblems.Games.Terms

import           Cryptography.ComputationalProblems.Abstract.Macro
import           Cryptography.ComputationalProblems.Abstract.Terms

abstractSS :: Note
abstractSS = subsection "Abstract computational problems" $ do
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


