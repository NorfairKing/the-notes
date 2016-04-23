module Cryptography.ComputationalProblems where

import           Notes                                    hiding (cyclic,
                                                           inverse)

import           Cryptography.SymmetricCryptography.Macro
import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Composition.Macro
import           Functions.Order.Terms
import           Groups.Macro
import           Groups.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Probability.Distributions.Macro
import           Probability.ProbabilityMeasure.Macro
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Relations.Orders.Macro
import           Relations.Orders.Terms                   hiding (order)
import           Rings.Macro
import           Rings.Terms
import           Sets.Basics.Terms

import           Cryptography.ComputationalProblems.Macro
import           Cryptography.ComputationalProblems.Terms


computationalProblemsS :: Note
computationalProblemsS = section "Computational Problems" $ do
    todo "Restructure this entire section, first abstract problems and performances, then search, etc"
    subsection "Search problems" $ do
        searchProblemDefinition

        distinctionProblemDefinition

        subsubsection "Function inversion" $ do
            functionInversionDefinition
            oneWayFunctionDefinition

        subsubsection "Discrete Logarithms" $ do
            discreteLogarithmProblemDefinition
            additiveDLEasy
            dlReducable
            dlModTwoInEvenOrderGroup
            dlNotation
            lsbProbNotation
            dlLSBHardness

        subsubsection "Diffie Hellman" $ do
            computationalDHProblemDefinition
            diffieHellmanTripleDefinition
            decisionalDHProblemDefinition


        gameDefinition
        solverDefinition
        performanceFunctionDefinition
        aSolverDefinition
        informationTheoreticalHardness
        worstCaseDefinition
        distributionCaseDefinition
        averageCaseDefinition
        averageCasePerformanceDifference
        probCaseNotation

    section "Reductions" $ do
        reductionDefinition
        compositionOfReductions
        todo "generalised reductions for lists of problems"


searchProblemDefinition :: Note
searchProblemDefinition = do
    de $ do
        lab searchProblemDefinitionLabel
        s ["A", searchProblem', "is a tuple", m sprob_, "consisting of an", instanceSpace', m isp_ <> ",", "a", witnessSpace', or, solutionSpace', m wsp_ <> ",", "a", predicate, m $ fun2 spred_ isp_ wsp_ bits , anda, probabilityDistribution, m sprob_, "over the", instanceSpace]
    nte $ do
        let x = "x"
            w = "w"
        s [the, searchProblem, m sprob_, "consists of finding, for a given instance", m (x ∈ isp_) <> ",", "drawn according to", m sprob_ <> ", a", witness, m (w ∈ wsp_), "such that", m $ sol x w, "holds"]


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

distinctionProblemDefinition :: Note
distinctionProblemDefinition = de $ do
    lab distinctionProblemDefinitionLabel
    let n = "n"
    s ["A", distinctionProblem', "is a", searchProblem, "where, for some", m (n ∈ naturals) <> ",", "the", instanceSpace, "is a", set, "of", m n <> "-tuples", "and the", witnessSpace, "is", m $ intmod n]

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














computationalDHProblemDefinition :: Note
computationalDHProblemDefinition = de $ do
    lab computationalDiffieHellmanDefinitionLabel
    lab cDHDefinitionLabel
    let a = "a"
        b = "b"
        g = "g"
    s [the, computationalDiffieHellman, "(" <> cDH' <> ")", "problem for a given", cyclic, group, m $ grp_ =: grp (genby g) grpop_, "is the problem of computing, for given group elements", m $ g ^ a, and, m $ g ^ b, "the group element", m $ g ^ (a * b)]

diffieHellmanTripleDefinition :: Note
diffieHellmanTripleDefinition = de $ do
    lab diffieHellmanTripleDefinitionLabel
    let a = "a"
        b = "b"
        c = "c"
        g = "g"
    s ["A", diffieHellmanTriple, "in a given", cyclic, group, m $ grp_ =: grp (genby g) grpop_, "is a triple of the form", m $ triple (g ^ a) (g ^ b) (g ^ (a * b)), "where", m a <> ",", m b, and, m c, "are hole numbers"]


decisionalDHProblemDefinition :: Note
decisionalDHProblemDefinition = de $ do
    lab computationalDiffieHellmanDefinitionLabel
    lab cDHDefinitionLabel
    let a = "a"
        b = "b"
        c = "c"
        g = "g"
    s [the, decisionalDiffieHellman', "(" <> dDH' <> ")", "problem for a given", cyclic, group, m $ grp_ =: grp (genby g) grpop_, "is the problem of determining whether, for given group elements", (m $ g ^ a) <> ",", m $ g ^ b, and, m $ g ^ c, "whether they are chosen randomly and independently from", m grps_, "or form a", diffieHellmanTriple]

functionInversionDefinition :: Note
functionInversionDefinition = do
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

gameDefinition :: Note
gameDefinition = de $ do
    lab gameDefinitionLabel
    lab winningConditionDefinitionLabel
    s ["A", game', "is a", searchProblem, "where every instance is an interactive proces with which a", witness, "(algorithm) can interact in several steps"]
    s [the, game, "is characterized by a special winning condition that the algorithm should provoke to win the game"]
    s ["In thi sence, a", searchProblem, "is a non-interactive", game]
    todo "redefine in terms of system algebra"


solverDefinition :: Note
solverDefinition = de $ do
    lab solverDefinitionLabel
    s ["A", solver', "is an algorithm that plays a", game]

performanceFunctionDefinition :: Note
performanceFunctionDefinition = nte $ do
    de $ do
        lab performanceDefinitionLabel
        lab performanceValueDefinitionLabel
        lab performanceFunctionDefinitionLabel
        let sl = "s"
        s ["Let", m probl_, "be a", searchProblem, and, m solvs_, "a", set, "of", solvers, for, m probl_]
        s ["Let", m perfs_, "be a", set, "of so-called", performanceValues, "associated with", m probl_]
        s ["A", performanceFunction, "is a", function, "as follows"]
        ma $ func perff_ solvs_ perfs_ sl (perf_ sl)
    nte $ do
        s ["Performance values are often real numbers, for example a success probability or a distinguishing advantage"]
        s ["In the simplest case, performance values are binary"]

aSolverDefinition :: Note
aSolverDefinition = de $ do
    s ["Let", m probl_, "be a", searchProblem, and, m solvs_, "a", set, "of", solvers, for, m probl_]
    let po = partord_
    s ["Let", m perfs_, "be the", set, performanceValues, "associated with", m probl_, "such that", m perfs_, "is equipped with a", partialOrder, m po]
    let a = "a"
    s ["A", solver, "for which the following holds is called an", nSolver' a, "for", m p]
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
    s ["We define the", weightedAverageCaseProblem', "over", m d, or, dProblem' d, m $ spdc d p, "as the abstract", problem, "for which any", solver <> "'s", performance, "is defined as the weighted average over all the", performances, "of the", solver, "for the", problems, "in", m p]
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
    s ["Usually a", searchProblem, m p, "is described with an implicit", instanceSpace]
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








