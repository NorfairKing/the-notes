module Topology.MetricSpace where

import           Notes

import           Functions.Distances    (distanceDefinitionLabel, metric,
                                         metricDefinitionLabel, pseudometric)

import           Functions.Basics.Macro

metricSpace :: Note
metricSpace = note "metric-space" $ do
    section "Metric Spaces"
    subsection "Pseudometric Spaces"
    pseudoMetricSpaceDefinition
    metricSpaces

metricSpaces :: Note
metricSpaces = do
  subsection "Metric Spaces"
  metricSpaceDefinition
  metricSpaceExamples

pseudoMetricSpace :: Note
pseudoMetricSpace = ix "pseudometric space"

pseudoMetricSpaceDefinitionLabel :: Label
pseudoMetricSpaceDefinitionLabel = Label Definition "pseudometric-space"

pseudoMetricSpaceDefinition :: Note
pseudoMetricSpaceDefinition = de $ do
  lab pseudoMetricSpaceDefinitionLabel
  s ["Let ", m topset, " be a set and ", m toppm, " a ", pseudometric, ref distanceDefinitionLabel, on, m topset]
  s ["The tuple ", m toppms, " is called a ", term "pseudometric space"]

metricSpaceDefinitionLabel :: Label
metricSpaceDefinitionLabel = Label Definition "metric-space"

metricSpaceDefinition :: Note
metricSpaceDefinition = de $ do
  lab metricSpaceDefinitionLabel
  s ["Let ", m topset, " be a set and ", m topm, " a ", metric, ref metricDefinitionLabel, on , m topset]
  s ["The tuple ", m topms, " is called a ", term "pseudometric space"]

metricSpaceExamples :: Note
metricSpaceExamples = do
  ex $ do
    s [m $ topms_ reals (func2 topm reals reals realsp a b (av $ a - b)), " is a metric space"]
    toprove

  where
    a = "a"
    b = "b"
