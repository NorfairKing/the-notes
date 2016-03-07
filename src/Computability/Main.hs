module Computability.Main where

import           Notes

import           Computability.FiniteStateAutomata (finiteStateAutomata)
import           Computability.Languages           (languages)
import           Computability.RegularExpressions  (regularExpressions)
import           Computability.Symbols             (symbols)

computability :: Note
computability = chapter "Computability" $ do
    symbols
    languages
    regularExpressions
    finiteStateAutomata

