module Probability.Distributions.Macro where

import           Types

import           Macro.MetaMacro

import           Functions.Application.Macro

distributedAs :: Note -> Note -> Note
distributedAs = binop $ comm0 "sim"

(~.) :: Note -> Note -> Note
(~.) = distributedAs

-- * Bernoulli

bernoulliD :: Note -> Note
bernoulliD = binomialD 1

bernoulliD_ :: Note
bernoulliD_ = bernoulliD "p"

-- * Binomial

binomialD :: Note -> Note -> Note
binomialD = fn2 $ mathcal "B"

binomialD_ :: Note
binomialD_ = binomialD "n" "p"


-- * Normal
normalD :: Note -- Mean
        -> Note -- Variance
        -> Note
normalD = fn2 $ mathcal "N"

-- * Uniform
uniformD_ :: Note
uniformD_ = mathcal "U"
