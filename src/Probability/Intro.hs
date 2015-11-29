module Probability.Intro (
    intro

  , bernoulliExperimentDefinitionLabel
  ) where

import           Notes

intro :: Notes
intro = notesPart "intro" introBody

introBody :: Note
introBody = do
  experimentDefinition
  universeDefinition
  eventDefinition
  bernoulliExperimentDefinition


experimentDefinition :: Note
experimentDefinition = de $ do
  s ["A ", term "stochastic experiment", " is an ", ix "experiment", " of which the outcome is not known beforehand"]

universeDefinition :: Note
universeDefinition = de $ do
  s ["The ", term "universe", " of a ", ix "stochastic experiment", " is the set of all possible outcomes"]
  s ["It is denoted as ", m pruniv]

eventDefinition :: Note
eventDefinition = de $ do
  s ["An ", term "event", " of a ", ix "stochastic experiment", " is a ", ix "subset", " of the ", ix "univers"]

bernoulliExperimentDefinitionLabel :: Label
bernoulliExperimentDefinitionLabel = Label Definition "bernoulli-experiment"

bernoulliExperimentDefinition :: Note
bernoulliExperimentDefinition = de $ do
  lab bernoulliExperimentDefinitionLabel
  s ["A ", term "Bernoulli experiment", " is a ", ix "stochastic experiment", " with only two possible outcomes"]


