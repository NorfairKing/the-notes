module Probability.RandomVariable.Terms where

import           Notes

makeDefs [
      "random variable"
    , "stochastic variable"
    , "probabillistic function"
    , "measure"
    , "Borel-measure"
    , "cumulative distribution function"
    , "CDF"
    , "distribution function"
    , "distribution"
    , "probability distribution"
    , "quantile function"
    , "quartile"
    , "quantile"
    , "median"
    , "independent copy"
    , "clone"
    , "discrete"
    , "discrete distribution"
    , "statistical distance"
    , "continuous"
    , "continuous distribution"
    , "probability density function"
    , "probability density"
    , "density"
    , "statistically independent"
    , "expected value"
    , "mean"
    , "covariance"
    , "correlation"
    , "variance"
    , "standard deviation"
    , "empirical mean"
    , "sample mean"
    , "Hoeffding's inequality"
    ]

makeThms [
      "Expectation of constant"
    , "Linearity of expectation"
    , "Variance in terms of expectation"
    , "statistical distance unamplifiable"
    , "Hoeffding's inequality"
    ]

xRv :: Note -> Note
xRv x = m x <> "-" <> randomVariable

xRvs :: Note -> Note
xRvs x = m x <> "-" <> randomVariable
