module Probability.Intro where

import           Notes

import           Sets.Basics.Terms

import           Probability.Intro.Macro
import           Probability.Intro.Terms

intro :: Note
intro = note "intro" introBody

introBody :: Note
introBody = do
    note "experiment" $ do
        experimentDefinition
        bernoulliExperimentDefinition
    note "universe" $ do
        universeDefinition
        universeExamples


experimentDefinition :: Note
experimentDefinition = de $ do
    s ["A ", stochasticExperiment', " is an ", experiment', " of which the outcome is not known beforehand"]

universeDefinition :: Note
universeDefinition = de $ do
    lab universeDefinitionLabel
    s ["The ", universe', " of a ", stochasticExperiment', " is the", set, "of all possible outcomes"]
    s ["It is denoted as ", m univ_]

universeExamples :: Note
universeExamples = ex $ do
    let h = "Heads"
        t = "Tails"
    s ["In the", stochasticExperiment, "of flipping up a single coin, the", universe, "is", m $ setofs [h,t]]

bernoulliExperimentDefinition :: Note
bernoulliExperimentDefinition = de $ do
    lab bernoulliExperimentDefinitionLabel
    s ["A ", bernoulliExperiment', " is a ", stochasticExperiment, " with only two possible outcomes"]


