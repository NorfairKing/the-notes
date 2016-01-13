module Statistics.Main where

import           Notes

import           Probability.RandomVariable.Terms
import           Sets.Basics.Terms

import           Statistics.Macro
import           Statistics.Terms

statisticsC :: Note
statisticsC = chapter "Statistics" $ do
    statisticalModelDefinition
    parameterSpaceDefinition
    parametricModelDefinition


statisticalModelDefinition :: Note
statisticalModelDefinition = de $ do
    lab statisticalModelDefinitionLabel
    s ["A", statisticalModel, m smod_, "is a", set, "of", distributions, "or a", set, "of", densities]

parameterSpaceDefinition :: Note
parameterSpaceDefinition = de $ do
    lab parameterSpaceDefinitionLabel
    s ["A", parameterSpace, m parsp_, "is a", set, "of", parameters]

parametricModelDefinition :: Note
parametricModelDefinition = de $ do
    lab parametricModelDefinitionLabel
    s ["A", parametricModel, m parmod_, "is a", set, " that can be parametrized by a", finite, " number of parameters"]
