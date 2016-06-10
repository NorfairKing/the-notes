module Cryptography.ComputationalProblems.Games.DistinctionProblems where

import           Notes                                                              hiding (cyclic, inverse)

import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Distances.Terms
import           Logic.FirstOrderLogic.Macro
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Relations.Orders.Macro
import           Sets.Basics.Terms

import           Cryptography.SymmetricCryptography.Macro

import           Cryptography.ComputationalProblems.Abstract.Macro
import           Cryptography.ComputationalProblems.Abstract.Terms

import           Cryptography.ComputationalProblems.Games.Abstract.Terms

import           Cryptography.ComputationalProblems.Games.DistinctionProblems.Macro
import           Cryptography.ComputationalProblems.Games.DistinctionProblems.Terms

distinctionProblemsSSS :: Note
distinctionProblemsSSS = subsubsection "Distinction problems" $ do
    deterministicDistinctionProblemDefinition
    deterministicDistinguisherDefinition
    probabillisticDistinguisherDefinition
    probabillisticDistinctionProblemDefinition
    distinguisherDeterministicDPDeterministicDistinguinger
    distinguisherDeterministicDPProbabilisticDistinguinger
    distinguisherProbabilisticDPDeterministicDistinguinger
    distinguisherProbabilisticDPProbabilisticDistinguinger
    bestDistinguisherAdvantage
    distinctionAdvantagePseudoMetric
    distinctionAdvantageRandomVariables
    splittingDistinctionProblem
    probabillisticDistinguishersAreNoBetterThanDeterministicDistinguishersTheorem
    distinguisherPerformanceDefinition

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
        s ["A", solver, "which, in this case, is called a", distinguisher', ",is supposed to guess which of the two objects it is given access to"]
        s ["Let", m ds, "be a", set, "of such abstract", distinguishers]
        let d = "d"
            o = "o"
        s ["A", function, m guess_, "as follows determines the guess of a given", distinguisher, m d, "when given access to a given object", m o]
        ma $ func2 guess_ ds (setofs [o0, o1]) bits d o $ guess d o
        let i = "i"
        s [m $ guess d o =: i, "is interpreted as", dquoted $ s [m d, "guesses that it sees", m $ o !: i, "when given", m o]]

probabillisticDistinguisherDefinition :: Note
probabillisticDistinguisherDefinition = de $ do
    let ds = mathcal "D"
    s ["Let", m ds, "be a", set, "of", deterministicDistinguishers]
    let dd = "D"
    s ["A", probabilisticDistinguisher', "is a", probabilityDistribution, m $ prdis_ dd, "of a", xRv ds]

    -- let o = "o"
    --     o0 = o !: 0
    --     o1 = o !: 1
    --     p = dprob o0 o1
    -- s ["A", function, m guess_, "as follows determines the guess of a given", probabilisticDistinguisher, m $ prdis_ dd, "when given access to a given object", m o, "in a", deterministicDistinctionProblem, m p]
    -- ma $ func2 guess_ (prdss ds) (setofs [o0, o1]) bits (prdis_ dd) o $ guess (prdis_ dd) o

probabillisticDistinctionProblemDefinition :: Note
probabillisticDistinctionProblemDefinition = do
    let o = "O"
        o0 = o !: 0
        o1 = o !: 1
    let p = dprob (prdis_ o0) (prdis_ o1)
    de $ do
        s ["Let", m objs_, "be a set of objects"]
        s ["Let", m $ prdis_ o0, and, m $ prdis_ o1, be, probabilityDistributions, "of", xRvs objs_, m o0, and, m o1]
        s [m p, "is then called a", probabilisticDistinctionProblem']

    nte $ do
        s ["Sometimes", m p, "is also denoted as", m $ dprob o0 o1, "but that is notation abuse"]

distinguisherDeterministicDPDeterministicDistinguinger :: Note
distinguisherDeterministicDPDeterministicDistinguinger = de $ do
    let o = "o"
        o0 = o !: 0
        o1 = o !: 1
        p = dprob o0 o1
        d = "d"
        ds = mathcal "D"
    s ["Let", m p, "be a", deterministicDistinctionProblem, and, m d, "a", deterministicDistinguisher, "from a set", m ds]
    s ["We define the", advantage', m $ dadv d o0 o1, "of", m d, "in", m p, "as follows"]
    ma $ dadv d o0 o1 =: guess d o1 - guess d o0

distinguisherDeterministicDPProbabilisticDistinguinger :: Note
distinguisherDeterministicDPProbabilisticDistinguinger = do
    let o = "o"
        o0 = o !: 0
        o1 = o !: 1
        p = dprob o0 o1
    let dd = "D"
        ds = mathcal dd
    de $ do
        s ["Let", m p, "be a", deterministicDistinctionProblem, and, m $ prdis_ dd, "a", probabilisticDistinguisher, over, m "a", set, m ds, "of", deterministicDistinguishers]
        s ["We define the", advantage', m $ dadv (prdis_ dd) o0 o1, "of", m $ prdis_ dd, "as follows"]
        ma $ dadv (prdis_ dd) o0 o1 =: prdis dd (guess dd o1 =: 1) - prdis dd (guess dd o0 =: 1)
    nte $ do
        s ["Sometimes", m $ dadv (prdis_ dd) o0 o1, "is also denoted as", m $ dadv dd o0 o1, "but that is notation abuse"]

distinguisherProbabilisticDPDeterministicDistinguinger :: Note
distinguisherProbabilisticDPDeterministicDistinguinger = do
    let oo = "O"
        oo0 = oo !: 0
        oo1 = oo !: 1
        pp = dprob (prdis_ oo0) (prdis_ oo1)
        d = "d"
    de $ do
        s ["Let", m pp, "be a", probabilisticDistinctionProblem, "for a set of objects", m objs_, "and let", m d, "be a", deterministicDistinguisher, for, m pp]
        s ["We define the", advantage', m $ dadv d (prdis_ oo0) (prdis_ oo1), "of", m d, "as follows"]
        ma $ dadv d (prdis_ oo0) (prdis_ oo1) =: prdis oo1 (guess d oo1 =: 1) - prdis oo0 (guess d oo0 =: 1)
    nte $ do
        s ["Sometimes", m $ dadv d (prdis_ oo0) (prdis_ oo1), "is also denoted as", m $ dadv d oo0 oo1, "but that is notation abuse"]

distinguisherProbabilisticDPProbabilisticDistinguinger :: Note
distinguisherProbabilisticDPProbabilisticDistinguinger = do
    let oo = "O"
        oo0 = oo !: 0
        oo1 = oo !: 1
        pp = dprob (prdis_ oo0) (prdis_ oo1)
    let ds = mathcal "D"
        dd = "D"
    de $ do
        s ["Let", m pp, "be a", probabilisticDistinctionProblem, "for a set of objects", m objs_]
        s ["Let", m ds, "be a", set, "of", deterministicDistinguishers, and, m $ prdis_ dd, a, probabilisticDistinguisher, for, m pp, on, m ds]
        s ["We define the", advantage', m $ dadv (prdis_ dd) (prdis_ oo0) (prdis_ oo1), "of", m $ prdis_ dd, "as follows"]
        ma $ dadv (prdis_ dd) (prdis_ oo0) (prdis_ oo1) =: prdiss [dd, oo1] (guess dd oo1 =: 1) - prdiss [dd, oo0] (guess dd oo0 =: 1)
    nte $ do
        s ["Sometimes", m $ dadv (prdis_ dd) (prdis_ oo0) (prdis_ oo1), "is also denoted as", m $ dadv dd oo0 oo1, "but that is notation abuse"]

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

probabillisticDistinguishersAreNoBetterThanDeterministicDistinguishersTheorem :: Note
probabillisticDistinguishersAreNoBetterThanDeterministicDistinguishersTheorem = thm $ do
    s ["For any", distinctionProblem <> ", the best", probabilisticDistinguisher, is, "as powerful as the best", deterministicDistinguisher]
    let ds = mathcal "D"
        dspd = prdss ds
        o = "o"
        o0 = o !: 0
        o1 = o !: 1
    ma $ dadv ds o0 o1 =: dadv dspd o0 o1

distinguisherPerformanceDefinition :: Note
distinguisherPerformanceDefinition = de $ do
    let ds = mathcal "D"
        dd = "D"
        o = "O"
        o0 = o !: 0
        o1 = o !: 1
        p = dprob o0 o1
    s ["In the context of a", distinctionProblem, m p, "we can view it as a", game, with, distinguishers, m dd, as, solvers]
    s [the, performanceValues, "are then in", m $ ccint (-1) 1, "and the", performanceFunction, "is defined as follows"]
    ma $ func (perff p) ds (ccint (-1) 1) dd $ perf p dd =: dadv dd o0 o1
