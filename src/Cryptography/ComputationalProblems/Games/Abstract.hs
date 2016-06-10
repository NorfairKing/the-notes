module Cryptography.ComputationalProblems.Games.Abstract where

import           Notes                                                   hiding (cyclic, inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Logic.PropositionalLogic.Macro
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Sets.Basics.Terms

import           Cryptography.ComputationalProblems.Abstract.Macro
import           Cryptography.ComputationalProblems.Abstract.Terms
import           Cryptography.SymmetricCryptography.Macro

import           Cryptography.ComputationalProblems.Games.Abstract.Macro
import           Cryptography.ComputationalProblems.Games.Abstract.Terms


abstractSSS :: Note
abstractSSS = subsubsection "Abstract Games" $ do
    deterministicGameDefinition
    performanceOfDeterministicWinnerInDeterministicGame
    probabillisticWinnerDefinition
    performanceOfProbabilisticWinnerInDeterministicGame
    probabillisticGameDefinition
    performanceOfDeterministicWinnerInProbabillisticGame
    performanceOfProbabilisticWinnerInProbabillisticGame
    multigameDefinition
    multiGameOrAndAndDefinition

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
