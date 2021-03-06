module Cryptography.ComputationalProblems where

import           Notes                                                              hiding (cyclic, inverse)

import           Functions.Application.Macro
import           Groups.Macro
import           Groups.Terms
import           Logic.PropositionalLogic.Macro
import           NumberTheory.Macro
import           NumberTheory.Terms
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Terms
import           Rings.Macro
import           Rings.Terms
import           Sets.Basics.Terms

import           Cryptography.SystemAlgebra.AbstractSystems.Terms
import           Cryptography.SystemAlgebra.DiscreteSystems.Terms

import           Cryptography.ComputationalProblems.Abstract
import           Cryptography.ComputationalProblems.Abstract.Macro
import           Cryptography.ComputationalProblems.Abstract.Terms
import           Cryptography.ComputationalProblems.Games
import           Cryptography.ComputationalProblems.Games.DistinctionProblems.Macro
import           Cryptography.ComputationalProblems.Games.Macro
import           Cryptography.ComputationalProblems.Games.Terms
import           Cryptography.ComputationalProblems.Reductions
import           Cryptography.ComputationalProblems.Reductions.Terms

import           Cryptography.ComputationalProblems.Macro
import           Cryptography.ComputationalProblems.Terms


computationalProblemsS :: Note
computationalProblemsS = section "Computational Problems" $ do
    abstractSS
    reductionsSS
    gamesSS


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





