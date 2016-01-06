module Probability.Independence where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Probability.ConditionalProbability.Macro
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.SigmaAlgebra.Macro
import           Sets.Basics.Terms

-- import           Probability.Independence.Macro
import           Probability.Independence.Terms


independenceS :: Note
independenceS = note "independence" $ do
    section "Independence"
    independenceDefinition
    dependenceDefinition
    conditionalProbabilityIndependentEvents
    pairwiseIndependenceDefinition
    mutualIndependenceDefinition
    mutualIndependenceImpliesPairwiseIndependence
    infiniteMutalIndependenceDefinition

psDec :: Note
psDec = s ["Let ", m prsp_, " be a ", probabilitySpace]

independenceDefinition :: Note
independenceDefinition = de $ do
    lab independentDefinitionLabel
    psDec
    s ["Two events ", m a, and, m b, " in ", m sa_, " are called ", independent', " if the following equality holds"]
    ma $ prob (a ∩ b) =: prob a * prob b

  where
    a = "A"
    b = "B"

dependenceDefinition :: Note
dependenceDefinition = de $ do
    psDec
    s ["If two events ", m a, and, m b, " in ", m sa_, " are not ", independent, ", they are called ", dependent', " events"]
    s ["This depedence is called.."]
    itemize $ do
        item $ s [positiveDependence', " if ", m (prob (a ∩ b) > prob a * prob b), " holds"]
        item $ s [negativeDependence', " if ", m (prob (a ∩ b) < prob a * prob b), " holds"]

  where
    a = "A"
    b = "B"

conditionalProbabilityIndependentEvents :: Note
conditionalProbabilityIndependentEvents = thm $ do
    psDec
    s ["Let ", m a, and, m b, " be two ", independent, " events in ", m sa_]
    ma $ cprob a b =: prob a

    proof $ do
        ma $ cprob a b =: prob (a ∩ b) /: prob b =: (prob a * prob b) /: prob b =: prob a

  where
    a = "A"
    b = "B"

pairwiseIndependenceDefinition :: Note
pairwiseIndependenceDefinition = de $ do
    s ["A set of events is called ", pairwiseIndependent', " if every two events in the set are ", independent]

mutualIndependenceDefinition :: Note
mutualIndependenceDefinition = de $ do
    psDec
    s ["A set ", m x, " of events is called ", mutuallyIndependent', " if the following holds"]
    ma $ fa (y ∈ powset x) $ prob (setincmp (a ∈ y) a) =: prodcmp (a ∈ y) (prob a)
  where
    a = "A"
    x = "X"
    y = "Y"

mutualIndependenceImpliesPairwiseIndependence :: Note
mutualIndependenceImpliesPairwiseIndependence = thm $ do
    s ["Mutual independence implies pairwise independence"]
    noproof

infiniteMutalIndependenceDefinition :: Note
infiniteMutalIndependenceDefinition = de $ do
    s ["An infinite ", set, " of events is called ", mutuallyIndependent, " if every finite subset is mutually independent"]




