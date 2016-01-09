module Logic.AbstractLogic where

import           Notes

import           Functions.Application.Macro

import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro

import           Logic.AbstractLogic.Macro
import           Logic.AbstractLogic.Terms

abstractLogic :: Note
abstractLogic = section "Abstract Logic" $ do
    s ["It is hard to speak about logic in a pure mathematical fashion as it originated, and still borders on, philosophy"]
    formulaDefinition
    theoryDefinition
    axiomSchemaDefinition
    theoremNotation
    knowledgeBaseDefinition
    entailmentDefinition
    inferenceDefinition
    inferenceNotation
    soundDefinition
    completeDefinition
    exampleTheoryIntegers
    exampleModusPonens



formulaDefinition :: Note
formulaDefinition = do
    de $ s ["A ", formula', " is a string of characters"]
    nte $ s ["In fact a formula can be equivalently be defined in other ways but this definition suffices"]


theoryDefinition :: Note
theoryDefinition = do
    de $ do
        lab theoryDefinitionLabel
        lab logicDefinitionLabel
        lab axiomDefinitionLabel
        lab grammarDefinitionLabel
        lab semanticsDefinitionLabel
        lab sentenceDefinitionLabel

        s ["A ", theory', or, logic',  " is a mathematical framework for proving properties about a certain object domain"]
        s ["Those properties are called ", theorem, "s"]
        s ["A ", theory, " consists of a ", grammar', ", a set of ", axiom', "s", and , semantics', " for formulae"]
        enumerate $ do
            item $ do
                s ["A ", grammar', " defines well-formed formulae"]
                s ["A well-formed ", formula, " is also called a ", sentence']
                s ["A ", formula', " represents an expression if it adheres to the ", grammar]
            item $ do
                s ["An ", axiom', " is a ", theorem, " that can be asserted without ", inference]
            item $ do
                s ["Semantics dictate the ", emph "meaning", " of formulae in the ", logic]
    nte $ do
        s ["Theorems are obtained from the axioms by a finite amount of applications of the inference rules"]


theoremNotation :: Note
theoremNotation = de $ do
    lab theoremDefinitionLabel
    s ["A ", theorem' , " ", m logicf, " is a well-formed formula that is provable in a ", theory, " ", m logict]
    s ["This is denoted as ", m (la logicf)]

knowledgeBaseDefinition :: Note
knowledgeBaseDefinition = de $ do
    lab knowledgeBaseDefinitionLabel
    s ["A ", knowledgeBase', " is a set of formulae"]
    s ["A ", knowledgeBase, " is called valid if all its formula are theorems in the given ", theory]

entailmentDefinition :: Note
entailmentDefinition = de $ do
    lab entailsDefinitionLabel
    s ["Let ", m logict , " be a ", theory, and, m lkb, " a ", knowledgeBase]
    s ["We say that a ", knowledgeBase, " ", m lkb, " ", entails', " a formula ", m alpha, " if ", m alpha, " is ", true, " for all valid ", knowledgeBase, "s ", m lkb]
    ma $ lkb `lent` alpha

inferenceDefinition :: Note
inferenceDefinition = de $ do
    lab inferenceDefinitionLabel
    s ["An ", inference', " ", m logicir, " in a theory ", m logict, " is a procedure for proving sentences from a ", knowledgeBase]
    s ["If a theorem ", m logict, " can be proven using ", m logicir, " we denote this as ", m (lpvm logicir "" logicf)]


inferenceNotation :: Note
inferenceNotation = de $ do
    s ["An inference rule is written as follows"]
    s ["It means that if theorems ", m (commaSeparated fs), " can be asserted, we may assert ", m (f 0), " as a theorem"]
    ma $ linf fs (f 0)
    s ["The sentences above the line are called the ", term "hypotheses", or, "antecedents", and, "the sentence below the line is called the ", term "conclusion"]
  where
    fs = [f 1, f 2, dotsc, f "n"]
    f n = logicf !: n

soundDefinition :: Note
soundDefinition = de $ do
    lab soundDefinitionLabel
    s ["An ", inference, " ", m "i", " is called ", sound', " if every ", theorem, " produced by ", m "i", " is a true ", formula]
    ma $ fa (commaSeparated [alpha, lkb]) (lpvm "i" lkb alpha ⇒ lkb `lent` alpha)

completeDefinition :: Note
completeDefinition = de $ do
    s ["An ", inference, " ", m "i", " is called ", complete', " if every true ", formula, " can be established as a theorem by ", m "i"]
    ma $ fa (commaSeparated [alpha, lkb]) (lkb `lent` alpha ⇒ lpvm "i" lkb alpha)

exampleModusPonens :: Note
exampleModusPonens = de $ do
    lab modusPonensDefinitionLabel
    s ["The ", modusPonens', " ", inference, " rule is common to many theories"]
    ma $ linf ["p", "p" ⇒ "q"] "q"

axiomSchemaDefinition :: Note
axiomSchemaDefinition = de $ s ["An axiom schema defines multiple (possibly even infinitely many) axioms via the use of a variable"]

exampleTheoryIntegers :: Note
exampleTheoryIntegers = ex $ do
    s ["Let ", m (mathbb "I"), " be a theory with a ", grammar , " ", m g, " a set ", m i, " of inference rules and a set ", m a , " of axioms"]
    enumerate $ do
        item $ do
            m g
            " defines a formula to be well-formed if it is of the following form: "
            itemize $ do
                item $ do
                  quoted $ m (i1 `eq` i2)
                  s [" where ", m (i1), " and ", m (i2), " are integer expressions"]
                item $ do
                  quoted $ m (i1 `lt` i2)
                  s [" where ", m (i1), " and ", m (i2), " are integer expressions"]
                item $ do
                  quoted $ m ((¬) b)
                  s [" where ", m b, " is a boolean expression"]
                item $ do
                  quoted $ m (b1 ⇒ b2)
                  s [" where ", m b1, " and ", m b2, " are boolean expressions"]
            s ["An ", quoted "integer expression", " is an expression of one the following forms"]
            itemize $ do
                item $ m 0
                item $ "A variable " <> m "n"
                item $ s [m (su "n"), " Where ", m "n", " is an integer expression"]
        item $ do
          "The axioms are "
          m (la $ 0 <: su 0)
          " and the axioms defined by the following axiom schema:"
          ma $ la $ "f" <: "g" ⇒ su "f" <: su "g"
    "In this example theory, the following could be a sound, but not complete, inference rule:"
    ma $ linf [su 0, fa "f" (p "f" ⇒ p (su "f"))] (fa "f" $ p "f")
    "This rule is called "
    term "induction"
    "."

  where
    p = fn "P"
    su = fn "S"
    i1 = "i" !: 1
    i2 = "i" !: 2
    b = "b"
    b1 = b !: 1
    b2 = b !: 2
    g = ("G" !: mathbb "I")
    i = ("I" !: mathbb "I")
    a = ("A" !: mathbb "I")









