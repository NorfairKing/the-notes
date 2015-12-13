module Computability.FiniteStateAutomata where

import           Notes

import           Computability.FiniteStateAutomata.Graph
import           Computability.FiniteStateAutomata.Macro
import           Computability.FiniteStateAutomata.Terms
--import           Computability.Languages.Macro
--import           Computability.Languages.Terms
import           Computability.Symbols.Macro
--import           Computability.Symbols.Terms

import           Functions.Basics.Macro

finiteStateAutomata :: Notes
finiteStateAutomata = notesPart "finite-state-automata" $ do
    section "Finite state automata"
    subsection "NFSA"
    nonDeterministicFiniteStateAutomatonDefinition
    nfsaExample
    todo "input word"
    todo "accepting run"
    todo "rejecting run"
    todo "language of NFSA"


    subsection "DFSA"
    deterministicFiniteStateAutomatonDefinition


nonDeterministicFiniteStateAutomatonDefinition :: Note
nonDeterministicFiniteStateAutomatonDefinition = de $ do
    s ["A ", nondeterministicFiniteStateAutomaton', " is a ", m 5, "-tuple ", m nfsa_, " where the following conents"]
    enumerate $ do
        item $ s [m nfas_, ": a finite set of states"]
        item $ s [m alph_, ": an alphabet"]
        item $ s [m $ fun nfatf_ (nfas_ ⨯ alphe_) (powset nfas_), ": A transition function"]
        item $ s [m $ nfass_, ": an initial state"]
        item $ s [m $ nfaas_, ": a set of accepting states"]

nfsaExample :: Note
nfsaExample = ex $ do
    fsaFig
        [a, b, c]
        a
        [c]
        [(a, b, p), (b, b, q), (b, c, p)] $
        s ["A ", nondeterministicFiniteStateAutomaton]
  where
    a = "a"
    b = "b"
    c = "c"
    p = "p"
    q = "q"


deterministicFiniteStateAutomatonDefinition :: Note
deterministicFiniteStateAutomatonDefinition = mempty
  -- s ["A ", term "deterministic finite state automaton", " (", term "DFSA", ") is a tuple "]

