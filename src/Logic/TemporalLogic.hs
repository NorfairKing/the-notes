module Logic.TemporalLogic where

import           Notes


import           Computability.Symbols.Macro
-- import           Functions.Application.Macro
import           Logic.AbstractLogic            (formula, grammar)
import           Logic.PropositionalLogic.Terms

import           Logic.TemporalLogic.Macro
import           Logic.TemporalLogic.Terms

temporalLogicS :: Note
temporalLogicS = note "temporal-logic" $ do
    section "Temporal Logic"
    subsection "Linear temporal logic"

    temporalLogicDefinition

    eventuallySemantics
    alwaysSemantics

    languageOfFormulaDefinition

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

    s ["The semantics are defined as follows"]
    s ["In ", linearTemporalLogic, " truth is evaluated with respect to a(n input) string"]
    s ["Let ", m $ (w =: strlist w1 w2 wn) ∈ strsof pp, " be a string"]
    s [m w, " satisfies a linear temporal logic ", formula, " ", m f, " at position ", m i, ", de:: Noted as ", m $ satis w i f, " under the following conditions"]
    itemize $ do
        item $ m $ ss p ⇔ p =: wi
        item $ m $ ss (not f) ⇔ not (ss f)
        item $ m $ ss (f ∧ g) ⇔ (pars $ ss f ∧ ss g)
        item $ m $ ss (f ∨ g) ⇔ (pars $ ss f ∨ ss g)
        item $ m $ ss (next f) ⇔ (pars $ i < n ∧ sw (i + 1) f)
        item $ m $ ss (f .∪ g) ⇔ (pars $ tes [i, j] $ (pars $ i < j <= n) ∧ sw j g ∧ (pars $ fa k $ (pars $ i <= k < j) ⇒ sw k f))
  where
    sw = satis w
    ss = sw i
    f = "f"
    g = "g"
    i = "i"
    j = "j"
    k = "k"
    n = "n"
    p = "p"
    pp = "P"
    w = "w"
    w1 = "w" !: 1
    w2 = "w" !: 2
    wi = "w" !: i
    wn = "w" !: n


eventuallySemantics :: Note
eventuallySemantics = thm $ do
    s ["Let ", m pp, " be a fixed set of propositions"]
    s ["Let ", m $ (w =: strlist w1 w2 wn) ∈ strsof pp, " be a string"]
    s ["The semantics of ", m $ ss $ evnt f, " can be rewritten as follows"]

    ma $ ss (evnt f) =: tes [i, j] ((pars $ i <= j <= n) ∧ sw j f)

    toprove
  where
    sw = satis w
    ss = sw i
    f = "f"
    i = "i"
    j = "j"
    pp = "P"
    n = "n"
    w = "w"
    w1 = "w" !: 1
    w2 = "w" !: 2
    wn = "w" !: n

alwaysSemantics :: Note
alwaysSemantics = thm $ do
    s ["Let ", m pp, " be a fixed set of propositions"]
    s ["Let ", m $ (w =: strlist w1 w2 wn) ∈ strsof pp, " be a string"]
    s ["The semantics of ", m $ ss $ alws f, " can be rewritten as follows"]

    ma $ ss (alws f) =: fas [i, j] ((pars $ i <= j <= n) ⇒ sw j f)

    toprove
  where
    sw = satis w
    ss = sw i
    f = "f"
    i = "i"
    j = "j"
    pp = "P"
    w = "w"
    n = "n"
    w1 = "w" !: 1
    w2 = "w" !: 2
    wn = "w" !: n

languageOfFormulaDefinition :: Note
languageOfFormulaDefinition = de $ do
    s ["The ", language', " of a ", linearTemporalLogic, " ", formula, " is the sets of strings that satisfy the formula"]
    ma $ languageOf f === setcmpr (w ∈ strsof pp) (satis w 1 f)
  where
    f = "f"
    w = "w"
    pp = "P"
