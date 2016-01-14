module Statistics.Main where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Terms
import           Probability.Distributions.Terms
import           Probability.Independence.Terms
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Sets.Basics.Terms

import           Statistics.Macro
import           Statistics.Terms

statisticsC :: Note
statisticsC = chapter "Statistics" $ do
    statisticalModelDefinition
    parameterSpaceDefinition
    parametricModelDefinition
    pointEstimation

statisticalModelDefinition :: Note
statisticalModelDefinition = de $ do
    lab statisticalModelDefinitionLabel
    s ["A", statisticalModel, m smod_, "is a", set, "of", distributions, "or a", set, "of", densities]

parameterSpaceDefinition :: Note
parameterSpaceDefinition = de $ do
    lab parameterSpaceDefinitionLabel
    s ["A", parameterSpace, m parsp_, "is a", set, "of all possible values of a", finite, set, "of", parameters]

parametricModelDefinition :: Note
parametricModelDefinition = de $ do
    lab parametricModelDefinitionLabel
    lab nonparametricModelDefinitionLabel
    s ["A", parametricModel, m parmod_, "is a", set, " that can be parametrized by a", finite, "number of parameters"]
    s ["A", nonparametricModel, "is a", set, "that cannot be parametrized by a", finite, "number of parameters"]

pointEstimation :: Note
pointEstimation = do
    pointEstimateDefinition
    biasDefinition

pointEstimateDefinition :: Note
pointEstimateDefinition = de $ do
    lab pointEstimateDefinitionLabel
    lab pointEstimatorDefinitionLabel
    let x = ("X" !:)
        n = "n"
    s ["Let", m $ lst (x 1) (x n), "be", m n, independent, and, identicallyDistributed, randomVariables, "from some distribution", m df_]
    s ["A", pointEstimator', or, pointEstimate, m pest_, "of a parameter", m par_, "is some", function, "of", m $ lst (x 1) (x n)]
    ma $ pest_ === fn "g" (lst (x 1) (x n))


biasDefinition :: Note
biasDefinition = de $ do
    lab biasDefinitionLabel
    s ["Let", m pest_, "be a", pointEstimator]
    s ["We define the", bias', m $ bs pest_, "of", m pest_, "as follows"]
    ma $ bs pest_ === ev pest_ - par_
    s ["A", pointEstimator, "is called", unbiased', "if its", bias, "is zero", ", that is, if its", expectedValue, "is", m par_]
