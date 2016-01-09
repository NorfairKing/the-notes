module Sets.PointedSets where

import           Notes

import           Sets.Basics.Terms

import           Sets.PointedSets.Macro
import           Sets.PointedSets.Terms

pointedSets :: Note
pointedSets = section "Pointed Sets" $ do
    pointedSetDefinition

pointedSetDefinition :: Note
pointedSetDefinition = de $ do
    lab pointedSetDefinitionLabel
    s ["Let ", m psetset_, " be a ", set, " and let ", m psetbase_, " be an ", element, " of ", m psetset_]
    s ["The tuple ", m pset_, " is called a ", pointedSet']
