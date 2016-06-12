module Cryptography.ComputationalProblems.Games where

import           Notes                                                          hiding (cyclic, inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Logic.PropositionalLogic.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Terms
import           Sets.Basics.Terms

import           Cryptography.SymmetricCryptography.Macro

import           Cryptography.ComputationalProblems.Abstract.Macro
import           Cryptography.ComputationalProblems.Abstract.Terms

import           Cryptography.ComputationalProblems.Games.Abstract
import           Cryptography.ComputationalProblems.Games.BitGuessingProblems
import           Cryptography.ComputationalProblems.Games.DiscreteGames
import           Cryptography.ComputationalProblems.Games.DistinctionProblems
import           Cryptography.ComputationalProblems.Games.HardnessAmplification

import           Cryptography.ComputationalProblems.Games.Macro
import           Cryptography.ComputationalProblems.Games.Terms


gamesSS :: Note
gamesSS = subsection "Games" $ do
    abstractSSS
    distinctionProblemsSSS
    bitGuessingProblemsSSS

    subsubsection "Search problems" $ do
        searchProblemDefinition
        searchProblemSolverDefinition
        searchProblemSolverRepetition
        functionInversionDefinition
        oneWayFunctionDefinition

    discreteGamesSSS
    hardnessAmplificationSSS

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

