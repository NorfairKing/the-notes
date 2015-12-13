module Probability.Distributions where

import           Notes

import           Probability.Intro (bernoulliExperimentDefinitionLabel)

distributions :: Note
distributions = note "important-distributions" body

body :: Note
body = do
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
  s [the, term "discrete uniform distribution", " is defined only on a finite universe: ", m (pruniv =: setlist (x 1) (x 2) (x n))]
  ma $ fa (i ∈ setlst 1 n) $ p i =: prob (setof $ x i) =: 1 /: n

  where
    x = subsc "x"
    p = subsc "p"
    n = "n"
    i = "i"

bernoulli :: Note
bernoulli = de $ do
  s ["A ", term "Bernoulli distribution", " is defined for a Bernoulli experiment", ref bernoulliExperimentDefinitionLabel]
  ma $ x ~. bernoulliD p
  ma $ cases $ do
    prob (x =: 1) & "" =: p
    lnbk
    prob (x =: 0) & "" =: q =: 1 - p
  s [m p, " is called the ", term "probability of success"]
  where
    x = "X"
    p = "p"
    q = "q"

binomial :: Note
binomial = de $ do
  s ["A ", term "binomial distribution", " is the distribution of the sum ", m y, " of ", m n, " times the same Bernoulli-distributed random variable ", m x, " with probability of success ", m p]
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
