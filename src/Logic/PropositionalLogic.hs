module Logic.PropositionalLogic (propositionalLogic) where

import           Logic.AbstractLogic
import           Notes

propositionalLogic :: Notes
propositionalLogic = notesPart "propositional-logic" body

body :: Note
body = do
  propositionalLogicDefinition
  logicalEquivalence

propositionalLogicDefinition :: Note
propositionalLogicDefinition = do
  de $ do
    s ["The ", term "propositional logic", " has a ", grammar, " ", m g, " and only two axioms."]
    enumerate $ do
      item $ do
        s [m g, " defines well formed formulas recursively with the following cases."]
        itemize $ do
          item $ s [dquoted "true", " and ", dquoted "false", " are sentences."]
          item $ s ["So-called propositional symbols, boolean variables, are sentences."]
          item $ s ["If ", m ss, " is a sentence, then ", m (neg ss), " is a sentence."]
          item $ s ["If ", m s1, " and ", m s2, " are sentences, then ", m (s1 ∨ s2), " is a sentence."]
          item $ s ["If ", m s1, " and ", m s2, " are sentences, then ", m (s1 ∧ s2), " is a sentence."]
      item $ do
        s ["The sentences ", dquoted "true", " and ", dquoted "false", " are respesctively asserted to be true and false."]
    s ["In propositional logic, a world defines a truth value to every propositional symbol."]

  nte $ do
    "There are some very common notational shorthands in propositional logic: "
    itemize $ do
      item $ s [dquoted (m $ s1 ⇒ s2), " for ", dquoted (m $ neg s1 ∨ s2)]
      item $ s [dquoted (m $ s1 ⇔ s2), " for ", dquoted (m $ (pars $ s1 ⇒ s2) ∧ (pars $ s2 ⇒ s1))]

  where
    ss = "S"
    s1 = ss !: 1
    s2 = ss !: 2
    g = ("G" !: mathbb "I")


logicalEquivalence :: Note
logicalEquivalence = mempty

