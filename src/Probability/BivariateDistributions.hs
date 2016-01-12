module Probability.BivariateDistributions where

import           Notes


import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Inverse.Macro
import           Logic.PropositionalLogic.Macro

import           Probability.Independence.Terms
import           Probability.Intro.Macro
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms

import           Probability.BivariateDistributions.Terms

bivariateDistributionS :: Note
bivariateDistributionS = section "Bivariate distributions" $ do
    stochasticTupleDefinition
    stochasticTupleInducesProbabilityMeasure
    bivariateDistributionFunctionDefinition
    bivariateDistributionFunctionProperties
    independenceOfRandomVariables

stochasticTupleDefinition :: Note
stochasticTupleDefinition = de $ do
    let x = "X"
        y = "Y"
    s ["Let", m x, and, m y, "be two", randomVariables, "in a", probabilitySpace, m prsp_]
    s ["The tuple", m $ tuple x y, "is called a", stochasticTuple', or, stochasticVector, "of dimension", m 2]
    ma $ func (tuple x y) univ_ (reals ^ 2) omega $ tuple (fn x omega) (fn y omega)

stochasticTupleInducesProbabilityMeasure :: Note
stochasticTupleInducesProbabilityMeasure = thm $ do
    let x = "X"
        y = "Y"
    s ["Let", m $ tuple x y, "be a", stochasticTuple]
    let p = prm_ !: (tuple x y)
    s ["This induces a", probabilityMeasure, m p]
    let a = "a"
        b = "b"
    ma $ fn p ((ocint minfty a) ⨯ (ocint minfty b)) =: prob (fn (inv x) (ocint minfty a) ∩ fn (inv y) (ocint minfty b))
    toprove

bivariateDistributionFunctionDefinition :: Note
bivariateDistributionFunctionDefinition = de $ do
    let x = "X"
        y = "Y"
    s ["Let", m $ tuple x y, "be a", stochasticTuple]
    s ["A", bivariateDistributionFunction, "is a", function, "as follows"]
    let d = df $ tuple x y
        a = "a"
        b = "b"
    ma $ func2 d reals reals reals a b $ prob (x <= a ∧ y <= b)

bivariateDistributionFunctionProperties :: Note
bivariateDistributionFunctionProperties = prop $ do
    let x = "X"
        y = "Y"
        d = df $ tuple x y
    s ["Let", m d, "be the", bivariateDistributionFunction, "of a", stochasticTuple, m $ tuple x y]
    let a = "a"
        b = "b"
    itemize $ do
        item $ s [m d, "is", increasing, "in every argument"]
        item $ s [m d, "is", rightCongruent, "in every argument"]
        item $ m $ lim a minfty (fn2 d a b) =: lim b minfty (fn2 d a b) =: 0
        item $ m $ lim2 a pinfty b pinfty (fn2 d a b) =: 1


independenceOfRandomVariables :: Note
independenceOfRandomVariables = de $ do
    s ["Let ", m x, and, m y, " be random variables in ", m prbsp]
    s [m x, and, m y, " are called ", independent', " if and only if every two events ", m (x <= a), and, m (y <= b), " are ", independent_, " events"]
  where
    a = "a"
    b = "b"
    x = "X"
    y = "Y"
