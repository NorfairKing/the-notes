module DataMining.LargeScaleLearning where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Geometry.AffineSpaces.Terms
import           Sets.Basics.Terms

import           DataMining.LargeScaleLearning.Macro
import           DataMining.LargeScaleLearning.Terms

largeScaleLearningS :: Note
largeScaleLearningS = section "Large scale learning" $ do
    onlineConvexProgrammingSS

onlineConvexProgrammingSS :: Note
onlineConvexProgrammingSS = subsection "Online convex programming" $ do
    convexProgrammingProblemDefinition
    regretDefinition
    onlineConvexProgrammingProblemDefinition

convexProgrammingProblemDefinition :: Note
convexProgrammingProblemDefinition = de $ do
    lab convexProgrammingProblemDefinitionLabel
    let xs = mathcal "X"
        c = "c"
        d = "d"
    s ["Let", m xs, "be a", convexSet_, "and a", subset, "of", m $ reals ^ d, "and let", m $ fun c xs realsp, "be a", convexFunction_]
    s ["The solution to a", convexProgrammingProblem', "consist of finding the element in", m xs, "that minimizes", m c]

regretDefinition :: Note
regretDefinition = de $ do
    lab regretDefinitionLabel
    lab optimalFeasableFixedPointDefinitionLabel
    lab averageRegretDefinitionLabel
    let xs = mathcal "X"
        c = "c"
        d = "d"
        t = "t"
        x = "x"
        n = "n"
    s ["Let", m xs, "be a", convexSet, "and a", subset, "of", m $ reals ^ d, "and let", m $ sequ c t, "be a", sequence, "of", convexFunctions]
    s ["Let", m $ sequ x t, "be a", sequence, "of points in", m xs]
    s [the, regret', "of", m $ sequ x t, "until round", m n, "is defined as follows"]
    ma $ reg n === pars (sumcmpr (t =: 1) n (fn (c !: t) (x !: t))) - opt n
    s ["Here, ", m $ opt n, "is the cost of the so-called", optimalFeasableFixedPoint']
    ma $ opt n === min (x ∈ xs) (sumcmpr (t =: 1) n (fn (c !: t) x))
    s [the, averageRegret', "is defined as follows"]
    ma $ areg n === (reg n /: n)


onlineConvexProgrammingProblemDefinition :: Note
onlineConvexProgrammingProblemDefinition = de $ do
    lab onlineConvexProgrammingProblemDefinitionLabel
    let xs = mathcal "X"
        c = "c"
        d = "d"
        t = "t"
        x = "x"
    s ["Let", m xs, "be a", convexSet, "and a", subset, "of", m $ reals ^ d, "and let", m $ sequ c t, "be a", sequence, "of", convexFunctions]
    s ["A", onlineConvexProgrammingProblem', "consists of, for each", m t, "sequentially, picking a point", m $ x ∈ xs, "that minimizes", m $ reg t]

