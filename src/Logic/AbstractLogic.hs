module Logic.AbstractLogic (abstractLogic) where

import           Notes

abstractLogic :: Notes
abstractLogic = notesPart "abstract-logic" body

body :: Note
body = do
  section "Abstract Logic"
  "It is hard to speak about logic in a pure mathematical fashion as it originated, and still borders on, philosophy."
  expressionDefinition
  theoryDefinition
  soundDefinition
  completeDefinition
  theoremNotation
  inferenceNotation
  modusPonensDefinition
  axiomSchemaDefinition
  exampleTheoryIntegers



expression :: Note
expression = ix "expression"

expressionDefinition :: Note
expressionDefinition = de $ do
  s ["A ", term "expression", " in logic is either true of false."]

formula :: Note
formula = ix "formula"

{-
formulaDefinition :: Note
formulaDefinition = de $ do
  s ["A ", term "formula", " is a string of character."]
-}

theory :: Note
theory = ix "theory"

grammar :: Note
grammar = ix "grammar"

axiom :: Note
axiom = ix "axiom"

theoryDefinition :: Note
theoryDefinition = de $ do
  s ["A ", term "theory", " is a mathematical framework for proving properties about a certain object domain."]
  s ["Those properties are called ", term "theorem", "s."]
  s ["A ", theory, " consists of a ", term "grammar", ", a set of ", term "axiom", "s and a set of ", term "inference rules."]
  enumerate $ do
    item $ do
      s ["A ", term "grammar", " defines well-formed formulae."]
      s ["A ", term "formula", " represents an ", expression, " if it adheres to the grammar."]
    item $ do
      s ["An ", term "inference rule", " describes how a new theorem can be obtained from previously obtained theorems."]
    item $ do
      s ["An ", term "axiom", " is a theorem that can be asserted without inference."]

  todo "Should this be more rigorous?"

soundDefinition :: Note
soundDefinition = de $ s ["A ", theory, " is called ", term "sound", " if every theorem is a true formula."]

completeDefinition :: Note
completeDefinition = de $ s ["A ", theory, " is called ", term "complete", " if every true formula can be established as a theorem."]

theoremNotation :: Note
theoremNotation = de $ do
  s ["Let ", m logicf, " be a well-formed formula in a theory ", m logict, "."]
  s ["This is denoted as ", m (logict <> lpv logicf), "."]

inferenceNotation :: Note
inferenceNotation = de $ do
  s ["An inference rule is written as follows."]
  s ["It means that if theorems ", m (commaSeparated fs), " can be asserted, we may assert ", m (f 0), " as a theorem."]
  ma $ linf fs (f 0)
  where
    fs = [f 1, f 2, dotsc, f "n"]
    f n = logicf !: n

modusPonensDefinition :: Note
modusPonensDefinition = de $ do
  s ["The ", term "modus ponens", " inference rule is common to many theories."]
  ma $ linf ["p", "p" ⇒ "q"] "q"

axiomSchemaDefinition :: Note
axiomSchemaDefinition = de $ do
  "An axiom schema defines multiple (possibly even infinitely many) axioms via the use of a variable."

exampleTheoryIntegers :: Note
exampleTheoryIntegers = ex $ do
  s ["Let ", m (mathbb "I"), " be a theory with a grammar ", m g, " a set ", m i, " of inference rules and a set ", m a , " of axioms."]
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
      m (lpv $ 0 <: su 0)
      " and the axioms defined by the following axiom schema:"
      ma $ lpv $ "f" <: "g" ⇒ su "f" <: su "g"
    item $ do
      m i
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









