module Probability.Distributions where

import           Notes

import           Logic.FirstOrderLogic.Macro
--import           Sets.Basics.Terms
import           LinearAlgebra.VectorSpaces.Terms

import           Probability.Intro.Macro
import           Probability.Intro.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Probability.SigmaAlgebra.Macro
import           Probability.SigmaAlgebra.Terms

import           Probability.Distributions.Macro
import           Probability.Distributions.Terms

distributions :: Note
distributions = section "Important distributions" $ do
    discreteDistributionSS
    continuousDistributionSS

discreteDistributionSS :: Note
discreteDistributionSS = subsection "Discrete distributions" $ do
    discreteUniform
    empiricalDistributionDefinition
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

empiricalDistributionDefinition :: Note
empiricalDistributionDefinition = de $ do
    let x = "X"
    s ["Let ", m x, "be a", vector, "of values"]
    s [m x, "viewed as the", universe, "of a", measurableSpace, m $ mspace x $ powset x, "induces a", probabilityMeasure, m prm_, "as follows"]
    let a = "a"
        b = "b"
    ma $ prob a =: (1 /: setsize x) * setsize (setcmpr (b ∈ x) (a =: b))
    s ["This is called the", empiricalDistribution', "defined by the vector", m x]


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
    ma $ do
        let x = "x"
        let k = "k"
        prob (x =: k) =: (n `choose` k) * p ^ k * (pars $ 1 - p) ^ (n - k)
  where
    i = "i"
    x = "X"
    y = "Y"
    n = "n"
    p = "p"

continuousDistributionSS :: Note
continuousDistributionSS = subsection "Continuous distributions" $ do
    gaussianDistributionDefinition

gaussianDistributionDefinition :: Note
gaussianDistributionDefinition = de $ do
    s ["A ", gaussianDistribution', or, normalDistribution', " with parameters ", m mn_, " and ", m var_, " is given by the following ", probabilityDensity]
    ma $ do
        let x = "x"
        prds x =: exp (- ((pars $ x - mn_) ^ 2) /: (2 * var_ ^ 2)) /: (var_ * sqrt (2 * pi))
