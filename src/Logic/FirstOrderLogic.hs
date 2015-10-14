module Logic.FirstOrderLogic (
    firstOrderLogic

  ) where

import           Notes

import           Logic.AbstractLogic (model, theory)

firstOrderLogic :: Notes
firstOrderLogic = notesPart "first-order-logic" body

body :: Note
body = do
  section "First Order Logic"
  firstOrderLogicDefinition
  atomicSentence
  compositeSentence
  quantifiers
  situationalCalculus


firstOrderLogicDefinition :: Note
firstOrderLogicDefinition = de $ do
  s ["While propositional logic is about simple facts, first order logic is about complex facts involving objects, relations, functions, etc..."]
  s [term "first order logic", " is a ", theory]
  s ["It is an extension of propositional logic with predicates, functions, variables and their quantifiers"]
  s ["Remember that these symbols are just that, symbols"]

  s ["A ", model, " in first order logic consists of instantiations of objects, relations and functions"]

atomicSentence :: Note
atomicSentence = do
  de $ s ["A sentence in first order logic is called ", term "atomic", " if it is a constant symbol or a function of only constant symbols"]
  exneeded

compositeSentence :: Note
compositeSentence = do
  de $ s ["A sentence in first order logic is called ", term "composite", " if it atomic, contains free variables an quantifiers, or is composed of composite sentences joined by connectives"]
  exneeded

quantifiers :: Note
quantifiers = do
  subsection "Quantifiers"
  s ["Quantifiers bind free variables"]
  existentialQuantifierDefinition
  universalQuantifierDefinition

  propertiesOfQuantifiers

x, y :: Note
x = "x"
y = "y"
p = "P"
pp :: Note -> Note
pp = funapp p
ppp x y = funapp p $ cs [x, y]
ppp x y = funapp p $ cs [x, y]

existentialQuantifierDefinition :: Note
existentialQuantifierDefinition = de $ do
  s ["The ", term "existential quantifier", " ", m existentialQuantifier, " "]
  s ["A sentence ", m (te x $ pp x), ", in the context of a model ", m "m", " is defined to hold true if there exists a ", m x, " in ", m "m", " such that the predicate ", m p, " holds for ", m x]

universalQuantifierDefinition :: Note
universalQuantifierDefinition = de $ do
  s ["The ", term "universal quantifier", " ", m universalQuantifier, " "]
  s ["A sentence ", m (fa x $ pp x), ", in the context of a model ", m "m", " is defined to hold true if the predicate ", m p, " holds for every instantiation of ", m x, " in ", m "m"]

propertiesOfQuantifiers :: Note
propertiesOfQuantifiers = do
  switchExistentials
  switchUniversals
  switchMixed
  dualityOfQuantifiers

switchExistentials :: Note
switchExistentials = thm $ do
  s ["The order of multiple contiguous existential quantifiers does not matter"]
  ma $ (pars $ te x $ te y $ ppp x y) ⇔ (pars $ te y $ te x $ ppp x y)

  toprove

switchUniversals :: Note
switchUniversals = thm $ do
  s ["The order of multiple contiguous universal quantifiers does not matter"]
  ma $ (pars $ fa x $ fa y $ ppp x y) ⇔ (pars $ fa y $ fa x $ ppp x y)

  toprove

switchMixed :: Note
switchMixed = cex $ do
  s ["The order of different quantifiers ", textbf "does", " matter"]
  ma $ not . pars $ (pars $ te x $ fa y $ ppp x y) ⇔ (pars $ fa y $ te x $ ppp x y)

  toprove

dualityOfQuantifiers :: Note
dualityOfQuantifiers = thm $ do
  s ["Each quantifier can be expressed in terms of the other"]
  ma $ (pars $ fa x $ pp x) ⇔ (pars $ not $ te x $ not $ pp x)

  toprove


situationalCalculus :: Note
situationalCalculus = do
  subsection "Situational Calculus"
  s ["The use of ", term "situational calculus", " is to model situations"]
  s ["In situational calculus, facts hold at a certain moment and/or in a certain situation"]
  s ["This is modeled by adding a situational argument to every non-eternal predicate"]

  s ["Situational calculus can be used to model change, non-change, actions, perceptions, etc..."]




  mempty
