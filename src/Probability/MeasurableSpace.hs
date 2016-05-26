module Probability.MeasurableSpace where

import           Notes

import           Probability.Intro.Macro
import           Probability.Intro.Terms
import           Probability.SigmaAlgebra.Macro
import           Probability.SigmaAlgebra.Terms

import           Probability.MeasurableSpace.Macro
import           Probability.MeasurableSpace.Terms


measurableSpaceS :: Note
measurableSpaceS = section "Measurable spaces" $ do
    measurableSpaceDefinition
    trivialMeasurableSpaceDefinition

measurableSpaceDefinition :: Note
measurableSpaceDefinition = de $ do
    s ["Let ", m univ_, " be the ", universe, " of a ", stochasticExperiment, " and let ", m sa_, " be a ", sa]
    s [m mspace_, " is called a ", measurableSpace']

trivialMeasurableSpaceDefinition :: Note
trivialMeasurableSpaceDefinition = de $ do
    lab trivialMeasurableSpaceDefinitionLabel
    s [m $ mspace univ_ $ setofs [emptyset, univ_], " is called the ", trivialMeasurableSpace]

