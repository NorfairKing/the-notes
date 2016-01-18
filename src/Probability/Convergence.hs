module Probability.Convergence where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro

import           Probability.ProbabilityMeasure.Macro
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms

import           Probability.Convergence.Macro
import           Probability.Convergence.Terms

convergenceS :: Note
convergenceS = section "Convergence of random variables" $ do
    s ["This part of probability is called", largeSampleTheory, or, limitTheory', or, asymptoticTheory']

    convergenceInProbabilityDefinition
    convergenceInDistributionDefinition
    convergenceInProbabilityImpliesConvergenceInDistribution
    todo "show that the reverse implication holds if X is a point distribution"
    convergenceInQuadraticMeanDefinition
    convergenceInQuadraticMeanImpliesConvergenceInProbability
    todo "show that the reverse implications don't hold"

convergenceInProbabilityDefinition :: Note
convergenceInProbabilityDefinition = de $ do
    let x = "X"
        i = "i"
    s ["Let", m $ sequ (x !: i) i, "be a", sequence, "of", randomVariables, "and let", m x, "be another", randomVariable]
    s [m $ sequ (x !: i) i, "is said to", convergeInProbability, "to", m x, "if the following holds"]
    let n = "n"
    ma $ x !: n -%> x === fa (epsilon ∈ realsp) (lim n pinfty (prob (abs $ x !: n - x) > epsilon) =: 0)

convergenceInDistributionDefinition :: Note
convergenceInDistributionDefinition = de $ do
    let x = "X"
        i = "i"
    s ["Let", m $ sequ (x !: i) i, "be a", sequence, "of", randomVariables, "and let", m x, "be another", randomVariable]
    let n = "n"
        t = "t"
        f = df_
    s ["Let", m $ f !: n, "denote the", cumulativeDistributionFunction, "of", m $ x !: n]
    s [m $ sequ (x !: i) i, "is said to", convergeInDistribution, "to", m x, "if the following holds"]
    ma $ x !: n -@> x === fa (t ∈ reals) (lim n pinfty (prdm (f !: n) t) =: prdm f t)

convergenceInProbabilityImpliesConvergenceInDistribution :: Note
convergenceInProbabilityImpliesConvergenceInDistribution = thm $ do
    let x = "X"
        i = "i"
        n = "n"
    s ["Let", m $ sequ (x !: i) i, "be a", sequence, "of", randomVariables, "and let", m x, "be another", randomVariable]
    ma $ (x !: n -%> x) ⇒ (x !: n -@> x)
    toprove


convergenceInQuadraticMeanDefinition :: Note
convergenceInQuadraticMeanDefinition = de $ do
    let x = "X"
        i = "i"
    s ["Let", m $ sequ (x !: i) i, "be a", sequence, "of", randomVariables, "and let", m x, "be another", randomVariable]
    let n = "n"
    s [m $ sequ (x !: i) i, "is said to", convergeInQuadraticMean, "to", m x, "if the following holds"]
    ma $ x !: n -#> x === lim n pinfty ((ev (x !: n - x)) ^ 2) =: 0

convergenceInQuadraticMeanImpliesConvergenceInProbability :: Note
convergenceInQuadraticMeanImpliesConvergenceInProbability = thm $ do
    let x = "X"
        i = "i"
        n = "n"
    s ["Let", m $ sequ (x !: i) i, "be a", sequence, "of", randomVariables, "and let", m x, "be another", randomVariable]
    ma $ (x !: n -#> x) ⇒ (x !: n -%> x)
    toprove
