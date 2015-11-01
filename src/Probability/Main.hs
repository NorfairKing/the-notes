module Probability.Main (probability) where

import           Notes

import           Probability.ConditionalProbability
import           Probability.Distributions
import           Probability.Independence
import           Probability.Intro
import           Probability.ProbabilityMeasure
import           Probability.RandomVariable
import           Probability.SigmaAlgebra

probability :: Notes
probability = notes "probability" $
  [
    header
  , intro
  , sigmaAlgebra
  , probabilityMeasure
  , conditionalProbability
  , independence
  , randomVariable
  , distributions
  ]

header :: Notes
header = notesPart "header" (chapter "Probability")
