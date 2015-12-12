module Computability.Main (
    computability
  ) where

import           Notes

import           Computability.FiniteStateAutomata (finiteStateAutomata)
import           Computability.Languages           (languages)
import           Computability.RegularExpressions  (regularExpressions)
import           Computability.Symbols             (symbols)

computability :: Notes
computability = notes "computability"
  [
    notesPart "header" (chapter "Computability")
  , symbols
  , languages
  , regularExpressions
  , finiteStateAutomata
  ]
