module Sets.PointedSets where

import           Notes

import           Sets.PointedSets.Macro

import           Sets.Basics            (element, set)

makeDefs [
    "pointed set"
    ]

pointedSets :: Note
pointedSets = note "pointed-set" $ do
    section "Pointed Sets"
    pointedSetDefinition

pointedSetDefinition :: Note
pointedSetDefinition = de $ do
    lab pointedSetDefinitionLabel
    s ["Let ", m psetset_, " be a ", set, " and let ", m psetbase_, " be an ", element, " of ", m psetset_]
    s ["The tuple ", m pset_, " is called a ", pointedSet']
