module Sets.Powerset where

import           Notes

import           Sets.Powerset.Terms

powersetS :: Note
powersetS = note "powerset" $ do
    powersetDefinition

powersetDefinition :: Note
powersetDefinition = de $ do
    lab powersetDefinitionLabel
    todo "powerset definition"
