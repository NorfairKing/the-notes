module Computability.Main (
    computability
  ) where

import           Notes

import           Computability.FiniteStateAutomata
import           Computability.Languages
import           Computability.Symbols

computability :: Notes
computability = notes "computability"
  [
    notesPart "header" (chapter "Computability")
  , symbols
  , languages
  , finiteStateAutomata
  ]
