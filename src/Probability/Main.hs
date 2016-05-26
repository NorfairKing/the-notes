module Probability.Main (probability) where

import           Notes

import           Probability.BayesianNetwork
import           Probability.BivariateDistributions
import           Probability.ConditionalProbability
import           Probability.Convergence
import           Probability.Distributions
import           Probability.Independence
import           Probability.Intro
import           Probability.LanguageModel
import           Probability.MeasurableSpace
import           Probability.ProbabilityMeasure
import           Probability.RandomVariable
import           Probability.SigmaAlgebra

probability :: Note
probability = chapter "Probability" $ do
    intro
    sigmaAlgebraS
    measurableSpaceS
    probabilityMeasureS
    conditionalProbabilityS
    independenceS
    randomVariableS
    distributions
    convergenceS
    bivariateDistributionS
    languageModels
    bayesianNetworkS
