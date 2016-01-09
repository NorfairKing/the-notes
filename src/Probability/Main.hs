module Probability.Main (probability) where

import           Notes

import           Probability.ConditionalProbability
import           Probability.Distributions
import           Probability.Independence
import           Probability.Intro
import           Probability.LanguageModel
import           Probability.ProbabilityMeasure
import           Probability.RandomVariable
import           Probability.SigmaAlgebra

probability :: Note
probability = chapter "Probability" $ do
    intro
    sigmaAlgebraS
    probabilityMeasureS
    conditionalProbabilityS
    independenceS
    randomVariableS
    distributions
    languageModels
