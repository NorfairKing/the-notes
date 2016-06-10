{-# LANGUAGE QuasiQuotes #-}
module Cryptography.ComputationalProblems.Games where

import           Notes                                             hiding
                                                                    (cyclic,
                                                                    inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Distances.Terms
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
import           Relations.Orders.Macro
import           Sets.Basics.Terms

import           Cryptography.SymmetricCryptography.Macro
import           Cryptography.SystemAlgebra.DiscreteSystems.Terms

import           Cryptography.ComputationalProblems.Abstract.Macro
import           Cryptography.ComputationalProblems.Abstract.Terms

import           Cryptography.ComputationalProblems.Games.Macro
import           Cryptography.ComputationalProblems.Games.Terms


gamesSS :: Note
gamesSS = subsection "Games" $ do
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

    subsubsection "Bit guessing problems" $ do
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

    subsubsection "Search problems" $ do
        searchProblemDefinition
        searchProblemSolverDefinition
        searchProblemSolverRepetition
        functionInversionDefinition
        oneWayFunctionDefinition

    subsubsection "Discrete games" $ do
        discreteGameDefinition
        discreteGameWinnerDefinition

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
    s ["A", probabilisticWinner', m $ prdis_ ww, "is a", probabilityDistribution, "of a", xRv dd, m ww]

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
    s ["A", probabilisticGame', m $ prdis_ gr, over, m gg, "is a", probabilityDistribution, "of a", xRv gg, m gr]

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

