module Probability.Distributions where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Probability.Intro.Macro
import           Probability.Intro.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.RandomVariable.Terms

import           Probability.Distributions.Macro
import           Probability.Distributions.Terms

distributions :: Note
distributions = note "important-distributions" $ do
    section "Important distributions"

    discreteDistributions
    continuousDistributions

discreteDistributions :: Note
discreteDistributions = do
    subsection "Discrete distributions"
    discreteUniform
    bernoulli
    binomial

discreteUniform :: Note
discreteUniform = de $ do
    s [the, discreteUniformDistribution', " is defined only on a ", finite, " ", universe, ": ", m (univ_ =: setlist (x 1) (x 2) (x n))]
    ma $ fa (i ∈ setlst 1 n) $ p i =: prob (setof $ x i) =: 1 /: n

  where
    x = subsc "x"
    p = subsc "p"
    n = "n"
    i = "i"

bernoulli :: Note
bernoulli = de $ do
    s ["A ", bernouilliDistribution', " is defined for a ", bernoulliExperiment_]
    ma $ x ~. bernoulliD p
    ma $ cases $ do
        prob (x =: 1) & "" =: p
        lnbk
        prob (x =: 0) & "" =: q =: 1 - p
    s [m p, " is called the ", probabilityOfSuccess]
  where
    x = "X"
    p = "p"
    q = "q"

binomial :: Note
binomial = de $ do
    s ["A ", binomialDistribution', " is the ", distribution, " of the sum ", m y, " of ", m n, " times the same Bernoulli-distributed ", randomVariable, " ", m x, " with ", probabilityOfSuccess, " ", m p]
    ma $ y ~. binomialD n p
    ma $ y =: sumcmpr (i =: 1) n (x !: i)
  where
    i = "i"
    x = "X"
    y = "Y"
    n = "n"
    p = "p"

continuousDistributions :: Note
continuousDistributions = do
    subsection "Continuous distributions"
    gaussianDistribution

gaussianDistribution :: Note
gaussianDistribution = de $ do
    s ["A ", gaussian', " ", distribution]
    todo gaussian
