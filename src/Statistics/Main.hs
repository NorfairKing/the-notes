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
    modifiedMeasuresDefinition
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
    s ["A", parametricModel, m parmod_, "is a", set, " that can be parametrized by a", finite, "number of", parameters]
    s ["A", nonparametricModel, "is a", set, "that cannot be parametrized by a", finite, "number of", parameters]

modifiedMeasuresDefinition :: Note
modifiedMeasuresDefinition = de $ do
    s ["Let", m parmod_, "be a", parametricModel, "and let", m par_, "be a", parameter]
    let c = cdot "" ""
    s [m $ probm par_ c, "is the probability, given", m par_]
    s ["Similarly we write", m $ evm par_ c, "to mean the", expectedValue, "given", m par_]
    s ["This is not the", expectedValue, "over all the parameters", m par_]
    s ["Similarly we also write", m $ varm par_ c, "to mean the", variance, "given", m par_]
    s ["This is not the", variance, "over all the parameters", m par_]

pointEstimation :: Note
pointEstimation = do
    pointEstimateDefinition
    consistentDefinition
    samplingDistributionDefinition
    standardErrorDefinition
    biasDefinition
    note "Mean squared error" $ do
        meanSquaredErrorDefinition
        meanSquaredErrorEquivalentDefinition

pointEstimateDefinition :: Note
pointEstimateDefinition = de $ do
    lab pointEstimateDefinitionLabel
    lab pointEstimatorDefinitionLabel
    let x = ("X" !:)
        n = "n"
    s ["Let", m $ lst (x 1) (x n), "be", m n, independent, and, identicallyDistributed, randomVariables, "from some distribution", m df_]
    s ["A", pointEstimator', or, pointEstimate, m pest_, "of a parameter", m par_, "is some", function, "of", m $ lst (x 1) (x n)]
    ma $ pest_ === fn "g" (lst (x 1) (x n))
    s ["The real parameter", m par_, "is unknow but fixed"]
    s ["The estimate", m pest_, "depends on", m $ lst (x 1) (x n), "and is therefore a", randomVariable]

consistentDefinition :: Note
consistentDefinition = de $ do
    lab consistentDefinitionLabel
    s ["A", pointEstimate, m pest_, "of a", parameter, m par_, "is called", consistent', "if it converges to", m par_, "in probability"]
    todo "Define convergence in probability"

samplingDistributionDefinition :: Note
samplingDistributionDefinition = de $ do
    s [the, distribution,  "of a", pointEstimate, m pest_, "is called the", samplingDistribution]

standardErrorDefinition :: Note
standardErrorDefinition = de $ do
    s [the, standardDeviation, "of a", pointEstimate, m pest_, "is called the", standardError]
    ma $ se pest_ === sqrt (var pest_)

biasDefinition :: Note
biasDefinition = de $ do
    lab biasDefinitionLabel
    lab unbiasedDefinitionLabel
    s ["Let", m pest_, "be a", pointEstimator]
    s ["We define the", bias', m $ bs par_ pest_, "of", m pest_, "as follows"]
    ma $ bs par_ pest_ === evm par_ pest_ - par_
    s ["A", pointEstimator, "is called", unbiased', "if its", bias, "is zero", ", that is, if its", expectedValue, "is", m par_]

meanSquaredErrorDefinition :: Note
meanSquaredErrorDefinition = de $ do
    lab meanSquaredErrorDefinitionLabel
    s ["Let", m pest_, "be a", pointEstimate]
    s [the, meanSquaredError, "is defined as follows"]
    ma $ mse pest_ === evm par_ ((pars $ pest_ - par_) ^ 2)
    todo "define this weird kind of expected value"

meanSquaredErrorEquivalentDefinition :: Note
meanSquaredErrorEquivalentDefinition = thm $ do
    s ["Let", m pest_, "be a", pointEstimate]
    ma $ mse pest_ =: varm par_ pest_ + (bs par_ pest_) ^ 2
    toprove
    aligneqs (mse pest_)
        [
          evm par_ ((pars $ pest_ - par_) ^ 2)
        , evm par_ ((pars $ pest_ - evm par_ pest_ + evm par_ pest_ - par_) ^ 2)
        , evm par_ ((pars $ (pars $ pest_ - evm par_ pest_) + (pars $ evm par_ pest_ - par_)) ^ 2)
        , evm par_ ((pars $ pest_ - evm par_ pest_) ^ 2 + 2 * (pars $ pest_ - evm par_ pest_) * (pars $ evm par_ pest_ - par_) + (pars $ evm par_ pest_ - par_) ^ 2)
        , evm par_ ((pars $ pest_ - evm par_ pest_) ^ 2)
        + 2 * evm par_ ((pars $ pest_ - evm par_ pest_) * (pars $ evm par_ pest_ - par_))
        + evm par_ ((pars $ evm par_ pest_ - par_) ^ 2)
        , evm par_ ((pars $ pest_ - evm par_ pest_) ^ 2)
        + 2 *  (pars $ evm par_ pest_ - par_) * evm par_ (pars $ pest_ - evm par_ pest_)
        + (pars $ evm par_ pest_ - par_) ^ 2
        , evm par_ ((pars $ pest_ - evm par_ pest_) ^ 2)
        + 2 *  (pars $ evm par_ pest_ - par_) * (pars $ cancel (evm par_ pest_) - cancel (evm par_ pest_))
        + (pars $ evm par_ pest_ - par_) ^ 2
        , evm par_ ((pars $ pest_ - evm par_ pest_) ^ 2)
        + (pars $ evm par_ pest_ - par_) ^ 2
        , varm par_ pest_ + (bs par_ pest_) ^ 2
        ]


