module Topology.MetricSpace where

import           Notes

import           Functions.Basics.Macro
import           Functions.Distances.Terms
import           Sets.Basics.Terms

import           Topology.MetricSpace.Terms

metricSpaceS :: Note
metricSpaceS = section "Metric Spaces" $ do
    pseudometricSpacesSS
    metricSpacesSS

pseudometricSpacesSS :: Note
pseudometricSpacesSS = subsection "Pseudometric Spaces" $ do
    pseudometricSpaceDefinition

metricSpacesSS :: Note
metricSpacesSS = subsection "Metric Spaces" $ do
    metricSpaceDefinition
    metricSpaceExamples

pseudometricSpaceDefinition :: Note
pseudometricSpaceDefinition = de $ do
    lab pseudometricSpaceDefinitionLabel
    s ["Let ", m topset, " be a ", set, and, m toppm, " a ", pseudometric_, on, m topset]
    s ["The tuple ", m toppms, " is called a ", pseudometricSpace']

metricSpaceDefinition :: Note
metricSpaceDefinition = de $ do
    lab metricSpaceDefinitionLabel
    s ["Let ", m topset, " be a ", set, and, m topm, " a ", metric_, on , m topset]
    s ["The tuple ", m topms, " is called a ", metricSpace']

metricSpaceExamples :: Note
metricSpaceExamples = do
    ex $ do
      s [m $ topms_ reals (func2 topm reals reals realsp a b (av $ a - b)), " is a ", metricSpace]
      toprove

  where
    a = "a"
    b = "b"
