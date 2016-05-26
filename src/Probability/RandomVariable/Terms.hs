module Probability.RandomVariable.Terms where

import           Notes

makeDefs [
      "random variable"
    , "stochastic variable"
    , "probabillistic function"
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
    , "conditional probability distribution"
    ]

makeThms [
      "Expectation of constant"
    , "Linearity of expectation"
    , "Variance in terms of expectation"
    , "statistical distance unamplifiable"
    , "Hoeffding's inequality"
    ]

xyRv :: Note -> Note -> Note
xyRv x y = m (tuple x y) <> "-" <> randomVariable

xyRv' :: Note -> Note -> Note
xyRv' x y = m (tuple x y) <> "-" <> randomVariable'

xyRvs :: Note -> Note -> Note
xyRvs x y = m (tuple x y) <> "-" <> randomVariables

yRv :: Note -> Note
yRv x = m x <> "-" <> randomVariable

yRvs :: Note -> Note
yRvs x = m x <> "-" <> randomVariable
