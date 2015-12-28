module Probability.Main (probability) where

import           Notes

import           Probability.ConditionalProbability
import           Probability.Distributions
import           Probability.Independence
import           Probability.Intro
import           Probability.ProbabilityMeasure
import           Probability.RandomVariable
import           Probability.SigmaAlgebra

probability :: Note
probability = note "probability" $ do
    chapter "Probability"
    intro
    sigmaAlgebraS
    probabilityMeasureS
    conditionalProbabilityS
    independenceS
    randomVariable
    distributions

