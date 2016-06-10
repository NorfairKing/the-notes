{-# LANGUAGE QuasiQuotes #-}
module Cryptography.ComputationalProblems.Games.BitGuessingProblems where

import           Notes                                                              hiding (cyclic, inverse)

import           Functions.Basics.Macro
import           Functions.Order.Terms
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
import           Sets.Basics.Terms

import           Cryptography.SymmetricCryptography.Macro

import           Cryptography.ComputationalProblems.Abstract.Macro
import           Cryptography.ComputationalProblems.Abstract.Terms

import           Cryptography.ComputationalProblems.Games.Abstract.Terms
import           Cryptography.ComputationalProblems.Games.DistinctionProblems.Macro
import           Cryptography.ComputationalProblems.Games.DistinctionProblems.Terms

import           Cryptography.ComputationalProblems.Games.BitGuessingProblems.Macro
import           Cryptography.ComputationalProblems.Games.BitGuessingProblems.Terms


bitGuessingProblemsSSS :: Note
bitGuessingProblemsSSS = subsubsection "Bit guessing problems" $ do
    s ["A", bitGuessingProblem', "is the abstract problem of guessing a hidden bit from a given object"]
    deterministicBitGuessingProblemDefinition
    deterministicBitGuesserDefinition
    advantageOfDeterministicBGInDeterministicBGP
    probabilisticBitGuesserDefinition
    advantageOfProbabilisticBGInDeterministicBGP
    probabilisticBitGuessingProblemDefinition
    advantageOfDeterministicBGInProbabilisticBGP
    advantageOfProbabilisticBGInProbabilisticBGP
    bitGuessingGamePerformanceDefinition
    distinctionBitGuessingEquivalenceLemma
    bitGuessingPerformanceAmplification

deterministicBitGuessingProblemDefinition :: Note
deterministicBitGuessingProblemDefinition = de $ do
    let o = "o"
        z = "z"
    s ["Let", m o, "be some object and", m $ z ∈ bits, "a bit"]
    s ["We then call", m $ bgprob o z, a, deterministicBitGuessingProblem']

deterministicBitGuesserDefinition :: Note
deterministicBitGuesserDefinition = de $ do
    let o = "o"
        z = "z"
    s ["A", bitGuesser, "is an abstract object that, given an object", m o, ", is supposed to guess the hidden bit in a", bitGuessingGame]
    let ds = "D"
        d = "d"
    s ["Let", m ds, "be a", set, "of such abstract", bitGuessers, "then a function", m guess_, "determines the guess of a given", deterministicBitGuesser']
    ma $ func guess_ ds bits d $ guess d o
    s [m $ guess d o =: z, "can be interpreted as the statement that the", deterministicBitGuesser, m d, "guesses the bit", m z, "upon receiving object", m o]

advantageOfDeterministicBGInDeterministicBGP :: Note
advantageOfDeterministicBGInDeterministicBGP = de $ do
    let o = "o"
        z = "z"
        d = "d"
        ds = mathcal "D"
        p = bgprob o z
    s ["Let", m p, "be a", deterministicBitGuessingProblem, and, m d, a, deterministicBitGuesser, for, m p, from, a, set, m ds]
    s ["We define the", advantage', m $ gadv p d, "of", m d, "in", m p, "as follows"]
    ma $ func (gadvf p) ds (ccint (-1) 1) d $ gadv p d =: 2 * (pars $ (pars $ 1 - abs (guess d o - z)) - (1 / 2))
    s ["Note that", m $ 1 - abs (guess d o - z), is, m 1, "if", m $ guess d o, equals, m z, and, m 0, otherwise]

probabilisticBitGuesserDefinition :: Note
probabilisticBitGuesserDefinition = de $ do
    let ds = mathcal "D"
        dd = "D"
    s ["Let", m ds, "be a", set, "of", deterministicBitGuessers]
    s ["A", probabilisticBitGuesser', m $ prdis_ dd, "is a", probabilityDistribution, "of a", xRv ds, m dd]

advantageOfProbabilisticBGInDeterministicBGP :: Note
advantageOfProbabilisticBGInDeterministicBGP = do
    let o = "o"
        z = "z"
        ds = mathcal "D"
        dd = "D"
        p = bgprob o z
    de $ do
        s ["Let", m $ bgprob o z, "be a", deterministicBitGuessingProblem]
        s ["Let", m ds, "be a", set, "of", deterministicBitGuessers, and, m $ prdis_ dd, a, probabilisticBitGuesser, over, m ds]
        s ["We define the", advantage', m $ gadv p (prdis_ dd), "of", m $ prdis_ dd, "in", m p, "as follows"]
        ma $ func (gadvf p) (prdss ds) (ccint (-1) 1) (prdis_ dd) $ gadv p (prdis_ dd) =: 2 * (pars $ (prdis dd $ guess dd o =: z) - (1 / 2))
    nte $ do
        s ["Often", m $ gadv p (prdis_ dd), "is also written as", m $ gadv p dd, "but that is notation abuse"]

probabilisticBitGuessingProblemDefinition :: Note
probabilisticBitGuessingProblemDefinition = do
    let os = objs_
        oo = "O"
        zz = "Z"
    de $ do
        s ["Let", m os, "be a", set, "of objects"]
        s ["A", probabilisticBitGuessingProblem', "is the combination of a", probabilityDistribution, m $ prdis_ oo, "of a", xRv os, m oo, anda, probabilityDistribution, m $ prdis_ zz, "of a", xRv bits, m zz]
        s ["It is often written as", m $ bgprob (prdis_ oo) (prdis_ zz)]
    nte $ do
        s ["Often this is also written as", m $ bgprob oo zz, "but that is notation abuse"]

advantageOfDeterministicBGInProbabilisticBGP :: Note
advantageOfDeterministicBGInProbabilisticBGP = do
    let oo = "O"
        zz = "Z"
        ds = mathcal "D"
        d = "d"
        pp = bgprob (prdis_ oo) (prdis_ zz)
    de $ do
        s ["Let", m pp, "be a", probabilisticBitGuessingProblem, "and let", m d, beA, deterministicBitGuesser, from, a, set, m ds]
        s ["We define the", advantage', m $ gadv pp d, "of", m d, "in", m pp, "as follows"]
        ma $ func (gadvf pp) ds (ccint (-1) 1) d $ gadv pp d =: 2 * (pars $ (prdiss [oo, zz] $ guess d oo =: zz) - (1 / 2))
    nte $ do
        s ["Often", m $ gadv pp d, "is also written as", m $ gadv (bgprob oo zz) d, "but that is notation abuse"]

advantageOfProbabilisticBGInProbabilisticBGP :: Note
advantageOfProbabilisticBGInProbabilisticBGP = do
    let ds = mathcal "D"
        dd = "D"
        oo = "O"
        zz = "Z"
        pp = bgprob (prdis_ oo) (prdis_ zz)
    de $ do
        s ["Let", m pp, "be a", probabilisticBitGuessingProblem, "and let", m $ prdis_ dd, beA, probabilisticBitGuesser]
        s ["We define the", advantage', m $ gadv pp (prdis_ dd), "of", m $ prdis_ dd, "in", m pp, "as follows"]
        ma $ func (gadvf pp) (prdss ds) (ccint (-1) 1) (prdis_ dd) $ gadv pp (prdis_ dd) =: 2 * (pars $ (prdiss [oo, zz, dd] $ guess dd oo =: zz) - (1 / 2))
    nte $ do
        s ["Often", m $ gadv pp (prdis_ dd), "is also written as", m $ gadv (bgprob oo zz) dd, "but that is notation abuse"]

bitGuessingGamePerformanceDefinition :: Note
bitGuessingGamePerformanceDefinition = de $ do
    let ds = mathcal "D"
        dd = "D"
        oo = "O"
        zz = "Z"
        pp = bgprob oo zz
    s ["In the context of a", bitGuessingGame, m pp, "we can view it as a", game, with, bitGuessers, m dd, as, solvers]
    s [the, performanceValues, "are then in", m $ ccint (-1) 1, "and the", performanceFunction, "is defined as follows"]
    ma $ func (perff pp) ds (ccint (-1) 1) dd $ perf pp dd =: gadv pp dd

distinctionBitGuessingEquivalenceLemma :: Note
distinctionBitGuessingEquivalenceLemma = lem $ do
    s [distinctionProblems, "can be regarded as a special case of", bitGuessingProblems, "where the bit is uniform"]
    let os = objs_
        ds = mathcal "D"
    s ["Let", m os, "be a", set, "of objects", and, m ds, a, set, "of", distinguishers]
    let oo = "O"
        o0 = oo !: 0
        o1 = oo !: 1
        dp = dprob o0 o1
    s ["Let", m dp, "be a", probabilisticDistinctionProblem]
    let uu = "U"
    s ["Let", m uu, "be a", xRv bits, "such that its", probabilityDistribution, "is uniform", m uniformD_]
    let ou = oo !: uu
    let bp = bgprob ou uu
    s ["Let", m bp, "be the", bitGuessingProblem, "of guessing", m uu, from, m ou]
    let dd = "D"
    ma $ fa dd $ perf bp dd =: perf dp dd
    proof $ do
        s ["Let", m dd, "be an arbitrary", distinguisher]
        aligneqs (perf bp dd)
            [ gadv bp dd
            , 2 * (pars $ (prdiss [ou, uu, dd] $ guess dd ou =: uu) - (1 / 2))
            , 2 * (pars $ (pars $ (1 / 2) * (prdiss [o0, dd] (guess dd o0 =: 0)) + (1 / 2) * (prdiss [o1, dd] (guess dd o1 =: 1))) - (1 / 2))
            , 2 * (pars $ (pars $ (1 / 2) * (pars $ 1 - prdiss [o0, dd] (guess dd o0 =: 1)) + (1 / 2) * (prdiss [o1, dd] (guess dd o1 =: 1))) - (1 / 2))
            , 2 * (pars $ (pars $ (1 / 2) - (1 / 2) * (prdiss [o0, dd] (guess dd o0 =: 1)) + (1 / 2) * (prdiss [o1, dd] (guess dd o1 =: 1))) - (1 / 2))
            , prdiss [o1, dd] (guess dd o1 =: 1) - prdiss [o0, dd] (guess dd o0 =: 1)
            , dadv dd o0 o1
            , perf dp dd
            ]
        s ["In the third step we used that a bit is either", m 0, or, m 1, "with each", probability, m $ 1 / 2, "in the case of the uniform", probabilityDistribution]

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

