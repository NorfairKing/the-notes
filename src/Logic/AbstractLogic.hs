module Logic.AbstractLogic (
    abstractLogic

  , expression
  , formula
  , theory
  , grammar
  , knowledgeBase
  , inference
  ) where

import           Notes

abstractLogic :: Notes
abstractLogic = notesPart "abstract-logic" body

body :: Note
body = do
  section "Abstract Logic"
  "It is hard to speak about logic in a pure mathematical fashion as it originated, and still borders on, philosophy."
  formulaDefinition
  theoryDefinition
  worldDefinition
  axiomSchemaDefinition
  knowledgeBaseDefinition
  theoremNotation
  entailmentDefinition
  modelDefinition
  modelsOfDefinition
  equivalentDefinitionEntailment
  inferenceDefinition
  inferenceNotation
  soundDefinition
  completeDefinition
  exampleTheoryIntegers
  exampleModusPonens



expression :: Note
expression = ix "expression"

formula :: Note
formula = ix "formula"

formulaDefinition :: Note
formulaDefinition = do
  de $ s ["A ", term "formula", " is a string of characters."]
  nte $ "In fact a formula can be equivalently be defined in other ways but this definition suffices."


theory :: Note
theory = ix "theory"

grammar :: Note
grammar = ix "grammar"

axiom :: Note
axiom = ix "axiom"

theoryDefinition :: Note
theoryDefinition = de $ do
  s ["A ", term "theory", " or ", term "logic",  " is a mathematical framework for proving properties about a certain object domain."]
  s ["Those properties are called ", term "theorem", "s."]
  s ["A ", theory, " consists of a ", term "grammar", " and a set of ", term "axiom", "s."]
  enumerate $ do
    item $ do
      s ["A ", term "grammar", " defines well-formed formulae."]
      s ["A well-formed formula is also called a ", term "sentence", "."]
      s ["A ", term "formula", " represents an ", expression, " if it adheres to the grammar."]
    item $ do
      s ["An ", term "axiom", " is a theorem that can be asserted without inference."]


worldDefinition :: Note
worldDefinition = de $ do
  s ["A logical ", term "world", " or ", term "model", " is a set of boolean expressions that are true within the framework of certain theory."]


knowledgeBase :: Note
knowledgeBase = ix "knowledge base"

knowledgeBaseDefinition :: Note
knowledgeBaseDefinition = de $ do
  s ["A ", term "knowledge base", " is a set of boolean expressions in the context of a certain logical world."]
  s ["In a given world, a valid knowledge base is a subset of that world."]

theoremNotation :: Note
theoremNotation = de $ do
  s ["A theorem ", m logicf, " is a well-formed formula that is provable in a theory ", m logict, "."]
  s ["This is denoted as ", m (la logicf), "."]

entailmentDefinition :: Note
entailmentDefinition = de $ do
  s ["Let ", m logict , " be a theory and ", m lkb, " a knowledge base."]
  s ["We say that a ", knowledgeBase, " ", m lkb, " ", term "entails", " a boolean expression ", m alpha, " if ", m alpha, " is true in all worlds where ", m lkb, " is a valid knowledge base."]

modelDefinition :: Note
modelDefinition = de $ do
  s ["We say a world ", m "m", " is a ", term "model", " of an expression ", m alpha, " if ", m alpha, " is true in ", m "m"]

modelsOfDefinition :: Note
modelsOfDefinition = do
  de $ s ["The set of all models of an expression ", m alpha, " is denoted as ", m (lmo alpha), "."]

  nte $ do
    s ["With a little notation overloading we also denote ", dquoted (s ["The intersection of the set of all models of the expressions in a set ", m "S"]), " as ", m (lmo "S")]
    ma $ lmo "S" `eq` setincmp ("s" ∈ "S") (lmo "s")


equivalentDefinitionEntailment :: Note
equivalentDefinitionEntailment = de $ do
  s ["Another way of expressing the fact that an expression ", m alpha, " is entailed by a ", knowledgeBase, " ", m lkb, ": ", m (lkb `lent` alpha), " is using models: "]
  ma $ lmo lkb ⊆ lmo alpha

inference :: Note
inference = ix "inference"

inferenceDefinition :: Note
inferenceDefinition = de $ do
  s ["An ", term "inference", " ", m logicir, " in a theory ", m logict, " is a procedure for proving sentences from a ", knowledgeBase, "."]
  s ["If a theorem ", m logict, " can be proven using ", m logicir, " we denote this as ", m (lpvm logicir "" logicf), "."]


inferenceNotation :: Note
inferenceNotation = de $ do
  s ["An inference rule is written as follows."]
  s ["It means that if theorems ", m (commaSeparated fs), " can be asserted, we may assert ", m (f 0), " as a theorem."]
  ma $ linf fs (f 0)
  where
    fs = [f 1, f 2, dotsc, f "n"]
    f n = logicf !: n


soundDefinition :: Note
soundDefinition = de $ do
  s ["An ", inference, " ", m "i", " is called ", term "sound", " if every theorem is a true formula:"]
  ma $ fa (commaSeparated [alpha, lkb]) (lpvm "i" lkb alpha ⇒ lkb `lent` alpha)

completeDefinition :: Note
completeDefinition = de $ do
  s ["An ", inference, " ", m "i", " is called ", term "complete", " if every true formula can be established as a theorem."]
  ma $ fa (commaSeparated [alpha, lkb]) (lkb `lent` alpha ⇒ lpvm "i" lkb alpha)

exampleModusPonens :: Note
exampleModusPonens = de $ do
  s ["The ", term "modus ponens", " inference rule is common to many theories."]
  ma $ linf ["p", "p" ⇒ "q"] "q"

axiomSchemaDefinition :: Note
axiomSchemaDefinition = de $ do
  "An axiom schema defines multiple (possibly even infinitely many) axioms via the use of a variable."

exampleTheoryIntegers :: Note
exampleTheoryIntegers = ex $ do
  s ["Let ", m (mathbb "I"), " be a theory with a ", grammar , " ", m g, " a set ", m i, " of inference rules and a set ", m a , " of axioms."]
  enumerate $ do
    item $ do
      m g
      " defines a formula to be well-formed if it is of the following form: "
      itemize $ do
        item $ do
          quoted $ m (i1 `eq` i2)
          s [" where ", m (i1), " and ", m (i2), " are integer expressions."]
        item $ do
          quoted $ m (i1 `lt` i2)
          s [" where ", m (i1), " and ", m (i2), " are integer expressions."]
        item $ do
          quoted $ m ((¬) b)
          s [" where ", m b, " is a boolean expression."]
        item $ do
          quoted $ m (b1 ⇒ b2)
          s [" where ", m b1, " and ", m b2, " are boolean expressions."]
      s ["An ", quoted "integer expression", " is an expression of one the following forms: "]
      itemize $ do
        item $ m 0
        item $ "A variable " <> m "n"
        item $ s [m (su "n"), " Where ", m "n", " is an integer expression."]
    item $ do
      "The axioms are "
      m (la $ 0 <: su 0)
      " and the axioms defined by the following axiom schema:"
      ma $ la $ "f" <: "g" ⇒ su "f" <: su "g"
  "In this example theory, the following could be a sound, but not complete, inference rule:"
  " contains only one inference rule: "
  ma $ linf [su 0, p "f" ⇒ p (su "f")] (p "f")

  where
    p = funapp "P"
    su = funapp "S"
    i1 = "i" !: 1
    i2 = "i" !: 2
    b = "b"
    b1 = b !: 1
    b2 = b !: 2
    g = ("G" !: mathbb "I")
    i = ("I" !: mathbb "I")
    a = ("A" !: mathbb "I")









