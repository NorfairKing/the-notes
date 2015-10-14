module Topology.Main (
    topologyNotes

  , topology
  ) where

import           Notes

topologyNotes :: Notes
topologyNotes = notes "topology" $
  [
    notesPart "header" (chapter "Topology")
  , notesPart "topological-spaces" topologicalSpaces
  ]

topologicalSpaces :: Note
topologicalSpaces = do
  topologyDefinition
  topologicalSpaceDefinition

topology :: Note
topology = ix "topology"

topologyDefinition :: Note
topologyDefinition = de $ do
  s ["Let ", m topset, " be a set"]
  s ["A ", term "topology", " ", m toptop, " on ", m topset, " is a collection of subsets of ", m topset, "with the following properties"]
  enumerate $ do
    item $ m $ emptyset ∈ toptop
    item $ m $ topset ∈ toptop
    item $ do
      s ["Let ", m "A", " be a subset of ", m toptop]
      ma $ setuncmp ("a" ∈ "A") "a" ∈ toptop
      s ["The union of any collection of open sets is an open set"]
    item $ do
      s ["Let ", m "B", " be a finite subset of ", m toptop]
      ma $ setincmp ("b" ∈ "B") "b" ∈ toptop
      s ["The intersection of any finite collection of open sets in an open set"]
  s ["These sets are called the ", term "open", " sets of ", m topset]


topologicalSpaceDefinition :: Note
topologicalSpaceDefinition = de $ do
  s ["Let ", m topset, " be a set and ", m toptop, " a topology on ", m topset]
  s [m topsp, " is called a ", term "topological space"]
