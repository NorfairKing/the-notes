module Probability.Intro where

import           Notes

import           Sets.Basics

import           Probability.Intro.Macro
import           Probability.Intro.Terms

intro :: Note
intro = note "intro" introBody

introBody :: Note
introBody = do
    experimentDefinition
    universeDefinition
    eventDefinition
    bernoulliExperimentDefinition


experimentDefinition :: Note
experimentDefinition = de $ do
    s ["A ", stochasticExperiment', " is an ", experiment', " of which the outcome is not known beforehand"]

universeDefinition :: Note
universeDefinition = de $ do
    lab universeDefinitionLabel
    s ["The ", universe', " of a ", stochasticExperiment', " is the set of all possible outcomes"]
    s ["It is denoted as ", m univ_]

eventDefinition :: Note
eventDefinition = de $ do
    s ["An ", event', " of a ", stochasticExperiment', " is a ", subset, " of the ", universe]

bernoulliExperimentDefinition :: Note
bernoulliExperimentDefinition = de $ do
    lab bernoulliExperimentDefinitionLabel
    s ["A ", bernoulliExperiment', " is a ", stochasticExperiment, " with only two possible outcomes"]


