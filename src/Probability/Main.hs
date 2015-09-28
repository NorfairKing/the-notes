module Probability.Main (probability) where

import           Notes

import           Probability.ProbabilityMeasure
import           Probability.RandomVariable
import           Probability.SigmaAlgebra

probability :: Notes
probability = notes "probability" $
  [
    header
  , sigmaAlgebra
  , probabilityMeasure
  , randomVariable
  ]

header :: Notes
header = notesPart "header" (notesChapter "Probability")
