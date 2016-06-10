module Probability.ConditionalProbability.Macro where

import           Types

import           Probability.ProbabilityMeasure.Macro

-- | Conditional probability
cprob :: Note -> Note -> Note
cprob n m = prob $ n <> commS ";" <> commS "middle" <> "|" <> commS ";" <> m
