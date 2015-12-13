module Logic.TemporalLogic where

import           Notes

import           Logic.AbstractLogic            (grammar)
import           Logic.PropositionalLogic.Terms

import           Logic.TemporalLogic.Macro
import           Logic.TemporalLogic.Terms

temporalLogicS :: Notes
temporalLogicS = notesPart "temporal-logic" $ do
    section "Temporal Logic"
    subsection "Linear temporal logic"
    temporalLogicDefinition

temporalLogicDefinition :: Note
temporalLogicDefinition = de $ do
    lab temporalLogicDefinitionLabel

    s [linearTemporalLogic', " is an extension of ", propositionalLogic_, " with temporal operators"]

    s ["Let ", m pp, " be a fixed set of propositions"]
    s ["The ", grammar, " of ", linearTemporalLogic, " is defined as follow"]
    ma $ p <> mid <> not f <> mid <> f ∧ g <> mid <> f ∨ g <> mid <> next f <> mid <> f .∪ g
    s ["Here, ", m p, " is an atomic proposition from ", m pp]
    itemize $ do
        item $ s ["Next: ", m $ next f]
        item $ s ["Until: ", m $ f .∪ g]

    s ["There are also some shorthand notations excluding the propositional shorthands"]
    itemize $ do
        item $ s ["Eventually: ", m $ evnt f === true .∪ f]
        item $ s ["Always: ", m $ alws f === (not $ evnt $ not f)]

  where
    p = "p"
    pp = "P"
    f = "f"
    g = "g"
