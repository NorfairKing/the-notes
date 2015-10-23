module Topology.Main (
    topology
  ) where

import           Notes

import           Topology.MetricSpace      (metricSpace)
import           Topology.TopologicalSpace (topologicalSpace)


topology :: Notes
topology = notes "topology" $
  [
    notesPart "header" (chapter "Topology")
  , topologicalSpace
  , metricSpace
  ]




