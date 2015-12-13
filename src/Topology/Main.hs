module Topology.Main where

import           Notes

import           Topology.MetricSpace      (metricSpace)
import           Topology.TopologicalSpace (topologicalSpace)


topology :: Note
topology = note "topology" $ do
    chapter "Topology"
    topologicalSpace
    metricSpace




