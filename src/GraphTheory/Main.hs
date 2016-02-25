module GraphTheory.Main where

import           Notes

import           Sets.Basics.Terms

import           GraphTheory.Macro
import           GraphTheory.Terms

graphTheory :: Note
graphTheory = chapter "Graph Theory" $ do
    graphDefinition

graphDefinition :: Note
graphDefinition = de $ do
    lab graphDefinitionLabel
    s ["A", graph', "is a tuple of two", sets, m grph_]
    itemize $ do
        item $ s [the, elements, "of", m vrt_, "are called", vertices']
        item $ s [the, elements, "of", m edg_, "are called", edges']
