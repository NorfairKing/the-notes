module Computability.FiniteStateAutomata where

import           Notes

import           Computability.FiniteStateAutomata.Macro
import           Computability.FiniteStateAutomata.Terms

finiteStateAutomata :: Notes
finiteStateAutomata = notesPart "finite-state-automata" body

body :: Note
body = do
  section "Finite state automata"
  nonDeterministicFiniteStateAutomatonDefinition
  deterministicFiniteStateAutomatonDefinition


nonDeterministicFiniteStateAutomatonDefinition :: Note
nonDeterministicFiniteStateAutomatonDefinition = de $ do
    s ["A ", nondeterministicFiniteStateAutomaton', " is a ", m 5, "-tuple ", m nfsa_, " where the following conents"]
    enumerate $ do
        item $ "hi"

deterministicFiniteStateAutomatonDefinition :: Note
deterministicFiniteStateAutomatonDefinition = mempty
  -- s ["A ", term "deterministic finite state automaton", " (", term "DFSA", ") is a tuple "]

