module Logic.HoareLogic (hoareLogic) where

import           Notes

import           Logic.AbstractLogic (inference, theory)

hoareLogic :: Notes
hoareLogic = notesPartRef "hoare-logic" body
  [softwareVerificationAxiomaticSemanticsSlides]

body :: Note
body = do
  section "Hoare Logic"
  hoareLogicDefinition
  hoareTripleNote
  ruleOfConsequence
  ruleOfConjunction
  sequentialComposition
  skipDefinition
  abortDefinition
  substitutionDefinition
  assignmentDefinition
  freeVariableDefinition
  modifiesDefinition
  ruleOfConstancy
  conditionalRule
  loopRule

  termination

  nocite softwareVerificationAxiomaticSemanticsSlides

a, b, c, i, p, q, r, e, x :: Note
a = "A"
b = "B"
c = "c"
i = "I"
p = "P"
q = "Q"
r = "R"
e = "e"
x = "x"

hoareLogicDefinition :: Note
hoareLogicDefinition = do
  s ["Hoare Logic is used to reason about imperative computer programs in abstract machines that have a state"]
  s ["A ", term "state", " is an assignment of values to abstract symbols"]
  s ["An instruction in such an abstract machine is a procedure of modifying that state"]
  de $ do
    s [term "Hoare logic", " is a ", theory]
    s ["In Hoare Logic, well-formed formulae are ", term "Hoare triple", "s"]
    ma $ htrip p a q
    s ["Here, ", m p, and, m q, " are assertions and ", m a, " is a sequence of instructions for an abstract machine"]
    s [m p, " is called the ", term "precondition", and, m q, " is called the ", term "postcondition"]
    s ["An assertion is a Boolean-valued function from the set of states"]
    s ["A true sencence in Hoare Logic describes the fact that the program ", m a, " will, started in any machine state satisfying ", m p, " will, if it terminates, yield a state satisfying ", m q]
    s ["This is called ", term "partial correctness"]
    s ["If a Hoare triple is partially correct and ", m a, " is guaranteed to ", textbf "terminate", " as well, it is called ", term "totally correct"]

hoareTripleNote :: Note
hoareTripleNote = nte $ do
  s ["An employee that needs to implement correct programs for given pre- and postconditions should look for the strongest preconditions and the weakest postconditions"]
  s ["Specifications as such will leave him with the least amount of work"]
  s ["The following Hoare specification woul give him the best job in the world"]
  ma $ htrip false a mempty
  s ["Any program ", m a, " is totally correct with respect to this specification"]
  newline
  s ["The second best job in the world would be the following specification"]
  ma $ htrip mempty a true
  s ["Any program ", m a, " is partially with respect to this specification"]
  s ["The only thing the programmer would have to do is to make sure that the program terminates as well"]

ruleOfConsequence :: Note
ruleOfConsequence = de $ do
  s [the, term "rule of conjunction", " is an ", inference, " in Hoare Logic"]
  ma $ linf [htrip p a q, p' ⇒ p, q ⇒ q'] (htrip p' a q')
  s ["A precondition can be replaced with a stronger precondition and a postcondition can be replaced by a weaker postcondition"]
  where
    p' = "P'"
    q' = "Q'"

ruleOfConjunction :: Note
ruleOfConjunction = de $ do
  s [the, term "rule of conjunction", " is an ", inference, " in Hoare Logic"]
  ma $ linf [htrip p a q, htrip p a r] $ htrip p a (q ∧ r)

sequentialComposition :: Note
sequentialComposition = de $ do
  s [the, term "rule of sequential composition", " is an ", inference, " in Hoare Logic"]
  ma $ linf [htrip p a q, htrip q b r] $ htrip p (a ؛ b) q

skip :: Note
skip = "skip"

skipDefinition :: Note
skipDefinition = de $ do
  s [the, term "skip", " Hoare triple is an axiom schema in Hoare Logic"]
  ma $ fa p $ htrip p skip p

abort :: Note
abort = "abort"

abortDefinition :: Note
abortDefinition = de $ do
  s [the, term "abort", " Hoare triple is an axiom schema in Hoare Logic"]
  ma $ fa p $ htrip false abort p

substitutionDefinition :: Note
substitutionDefinition = de $ do
  s [m (ass p e x), " is the expression obtained from ", m p, " by replacing every occurence of ", m x, by, m e]
  s ["Read it as ", dquoted (s [m p, " with ", m e, " instead of ", m x, "."])]

  exneeded

assignmentDefinition :: Note
assignmentDefinition = de $ do
  s [term "assignment", " is an axiom schema in Hoare Logic"]
  ma $ fa (cs [p,e,x]) $ htrip (ass p e x) (x =:= e) p

  exneeded

freeVariableDefinition :: Note
freeVariableDefinition = de $ do
  s ["A variable ", m x, " is said to be a ", term "free variable", " in an expression ", m p, " if ", m p, " doesn't quantify ", m x, " either existentially or universally"]
  newline
  s [m (freevars p), " is the set of all free variables in an expression ", m p]

modifiesDefinition :: Note
modifiesDefinition = de $ do
  s ["A program ", m a, " is said to ", term "modify", " a variable ", m x, " if at any point, ", m a, " assigns to ", m x]
  newline
  s [m (modifies a), " is the set of all variables that ", m a, " modifies"]

ruleOfConstancy :: Note
ruleOfConstancy = de $ do
  s [the, term "rule of constancy", " is an ", inference, " in Hoare Logic"]
  s ["Let ", m r, " be an assertion"]
  ma $ linf [htrip p a q, (freevars r) ∩ (modifies a) =§= emptyset] (htrip (p ∧ r) a (q ∧ r))
  s ["This is known as ", dquoted (s ["Whatever ", m a, " doesn't modify, stays the same."])]

  exneeded

conditionalRule :: Note
conditionalRule = de $ do
  s [the, term "conditional rule", " is an ", inference, " in Hoare Logic."]
  ma $ linf [htrip (p ∧ c) a q, htrip (p ∧ not c) b q] $ htrip p (ifThenElse c a b) q

  exneeded

loopRule :: Note
loopRule = de $ do
  s [the, term "loop rule", " is an ", inference, " in Hoare Logic"]
  ma $ linf [htrip p a i, htrip (i ∧ not c) b i] $ htrip p (fromUntilLoop a c b) (i ∧ c)
  s ["The first triple is called the ", term "initiation", and, " the second is called the ", term "consecution", or, term "inductiveness"]
  s ["This rule is also sometimes written as follows"]
  ma $ linf [htrip p a i, htrip (i ∧ not c) b i, brac (i ∧ c ⇒ q)] $ htrip p (fromUntilLoop a c b) q

termination :: Note
termination = do
  subsection "Termination"
  s ["To show total correctness, rather than just partial correctness, termination must also be proven"]
  s ["Termination is asserted for all but the loop triples if all the antecedents terminate"]

  loopTermination

loopTermination :: Note
loopTermination = de $ do
  s ["To prove the total correctness of a loop triple, we must first prove partial correctness and then loop termination as follows"]
  s ["There must exist a set ", m ss, " with a total ordering ", m ("" <= ""), " such that ", m ss, " has a least element ", m bot, " with respect to ", m ("" <= "")]
  s ["Three more conditions must hold"]

  enumerate $ do
    item $ m $ htrip p a (0 <> "< v")
    item $ do
      m $ brac $ bot <> "< v"
      " is an invariant of the loop."
    item $ do
      m v
      " decreases with ever iteration."
      ma $ fa v0 ((v <> "<" <> v0) ⇒ (htrip ((v =: v0) ∧ not c) b (v <> "<" <> v0)))

  where
    ss = "S"
    v = "v"
    v0 = "v" !: 0


softwareVerificationAxiomaticSemanticsSlides :: Reference
softwareVerificationAxiomaticSemanticsSlides = Reference lectureSlides "software-verification-axiomatic-semantics-part1" $
  [
    ("author", "Bertrand Meyer")
  , ("title", "Lecture 2: Axiomatic Semantics")
  , ("year", "2015")
  , ("month", "September")
  , ("note", "Lecture Slides")
  ]
