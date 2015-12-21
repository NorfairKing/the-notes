module Computability.FiniteStateAutomata where

import           Notes

import           Computability.Symbols.Macro
import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Logic.FirstOrderLogic.Macro

import           Computability.FiniteStateAutomata.Graph
import           Computability.FiniteStateAutomata.Macro
import           Computability.FiniteStateAutomata.Terms

finiteStateAutomata :: Note
finiteStateAutomata = note "finite-state-automata" $ do
    section "Finite state automata"
    subsection "NFSA"
    nonDeterministicFiniteStateAutomatonDefinition
    nfsaExample
    acceptanceDefinition
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

acceptanceDefinition :: Note
acceptanceDefinition = do
    de $ do
        lab acceptDefinitionLabel
        lab rejectDefinitionLabel
        s ["A ", nondeterministicFiniteStateAutomaton, " is said to ", accept', " a string ", m $ str_ =: strlist s1 s2 sn, ", also called an input word, if there exists a sequence of states ", m $ strlist r1 r2 rn, " as follows"]
        itemize $ do
            item $ s ["It starts in the initial state: ", m $ r1 =: nfass_]
            item $ s ["It ends in an accepting state: ", m $ rn ∈ nfaas_]
            item $ do
                "It respects the transition function: "
                ma $ fa (i ∈ setlst 1 n) $ r !: (i + 1) ∈ (fn2 nfatf_ ri si)
                s ["Note that this is slightly more simply specified than is actually the case"]
                s ["To make this simplification work, you must assume that between any two symbols in ", m str_, " the empty string ", m estr, " can be inserted if the transition function's symbol is ", m estr]
        s ["A ", nondeterministicFiniteStateAutomaton, " is said to ", reject', " a string ", m str_, " if it does not accept it"]
    ex $ do
        fsaFig
            [a, b]
            a
            [b]
            [(a, b, p), (b, b, q)] $
            s ["A ", nondeterministicFiniteStateAutomaton]
        s ["This ", nondeterministicFiniteStateAutomaton, " accepts the strings ", m $ cs ["p", "pq", "pqq", "pqqq", "..."]]

  where
    a = "a"
    b = "b"
    p = "p"
    q = "q"
    i = "i"
    r = "r"
    n = "n"
    r1 = r !: 1
    r2 = r !: 2
    ri = r !: i
    rn = r !: n
    s1 = "s" !: 1
    s2 = "s" !: 2
    si = "s" !: i
    sn = "s" !: n


deterministicFiniteStateAutomatonDefinition :: Note
deterministicFiniteStateAutomatonDefinition = mempty
    -- s ["A ", term "deterministic finite state automaton", " (", term "DFSA", ") is a tuple "]

