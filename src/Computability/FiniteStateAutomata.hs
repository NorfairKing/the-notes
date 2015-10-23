module Computability.FiniteStateAutomata (
   finiteStateAutomata
  ) where

import           Notes

finiteStateAutomata :: Notes
finiteStateAutomata = notesPart "finite-state-automata" body

body :: Note
body = mempty
  -- section "Finite state automata"
  -- nonDeterministicFiniteStateAutomatonDefinition
  -- deterministicFiniteStateAutomatonDefinition

deterministicFiniteStateAutomatonDefinition :: Note
deterministicFiniteStateAutomatonDefinition = de $ mempty
  -- s ["A ", term "deterministic finite state automaton", " (", term "DFSA", ") is a tuple "]

nonDeterministicFiniteStateAutomatonDefinition :: Note
nonDeterministicFiniteStateAutomatonDefinition = de $ mempty


