module Logic.HoareLogic where

import           Notes

import           Logic.AbstractLogic               (axiomSchema, formula,
                                                    inference, theory)
import           Sets.Basics                       (predicate)

import           Logic.HoareLogic.ExamQuestion2014
import           Logic.HoareLogic.Macro
import           Logic.HoareLogic.Terms
import           Relations.Orders.Macro

hoareLogicS :: Note
hoareLogicS = note "hoare-logic" $ do
    section "Hoare Logic"
    s [hoareLogic', " is used to reason about imperative computer programs in abstract machines that have a ", state]

    stateDefinition
    evaluationDefinition
    instructionDefinition
    assertionDefinition
    satisfactionExamples
    variableAssignmentDefinition

    hoareLogicDefinition
    hoareTripleNote

    ruleOfConsequenceDefinition
    ruleOfConjunctionDefinition
    sequentialCompositionDefinition

    skipDefinition
    abortDefinition
    substitutionDefinition
    assignmentDefinition
    forwardAssignmentDefinition
    freeVariableDefinition
    modifiesDefinition
    ruleOfConstancy
    conditionalRule
    loopRuleDefinition

    termination
    exampleProof

    nocite softwareVerificationAxiomaticSemanticsSlides

    examQuestion2014

a, b, c, i, p, q, r, e, x, y, z :: Note
a = "A"
b = "B"
c = "c"
i = "I"
p = "P"
q = "Q"
r = "R"
e = "e"
x = "x"
y = "y"
z = "z"

stateDefinition :: Note
stateDefinition = do
    de $ do
        lab stateDefinitionLabel
        s ["A ",state', " is an assignment of values to abstract symbols"]
    nte $ do
        s ["In computers these values are typically finite strings of bits but they can be arbitrary values in theory"]
        s ["In logical reasoning, the values are typically (unbounded) integers"]
    ex $ do
        s [m $ cs ["a" .-> 4, "b" .-> 3], " could be a ", state]

evaluationDefinition :: Note
evaluationDefinition = de $ do
    lab evaluationDefinitionLabel
    s ["The ", evaluation', " ", m $ b .: ss, " of a symbol ", m b, " with respect to a program state ", m ss, " is the value of ", m b, " in ", m ss]
    ma $ (b .: ss) =: a ⇔ ((b .-> a) ∈ a)
  where
    a = "a"
    b = "b"
    ss = "S"

instructionDefinition :: Note
instructionDefinition = do
    de $ do
        lab instructionDefinitionLabel
        s ["An ", instruction', " in such an abstract machine is a procedure of modifying that ", state]
    nte $ do
        s ["While we say ", quoted "modify", " it is perfectly valid to model a modification as a reconstruction with different variables"]
        s ["There is no real difference in math, but this difference manifests itself physically in real machines"]

assertionDefinition :: Note
assertionDefinition = de $ do
    lab assertionDefinitionLabel
    lab satisfiesDefinitionLabel
    s ["An ", assertion', " is a predicate on the set of posssible program states"]
    s ["A program ", state," ", m ss, " ", satisfies', " an ", assertion, " if the ", assertion, " holds for that program state"]
    todo "define assertions recursively, see the separation logic part"
  where ss = "S"

satisfactionExamples :: Note
satisfactionExamples = do
    ex $ m $ cs [x .-> 5, y .-> 10] |= ((x < y) ∧ (x > 0))
    ex $ do
        s [m $ x .-> 25 |= te y (y > x), " holds"]
        s ["Note that the ", m y, " doesn't have to be the value of a variable"]

variableAssignmentDefinition :: Note
variableAssignmentDefinition = do
    de $ do
        s [m $ a =:= b, " represents the instruction to assign the value of ", m b, " to the variable a"]
    ex $ do
        s ["If the program state holds ", m $ cs [a .-> 3, b .-> 5], " and the instruction ", m $ a =:= b, " is performed, the state afterwards would be ", m $ cs [a .-> 5, b .-> 5]]
  where
    a = "a"
    b = "b"

hoareLogicDefinition :: Note
hoareLogicDefinition = do
    de $ do
        lab hoareLogicDefinitionLabel
        lab hoareTripleDefinitionLabel
        lab preconditionDefinitionLabel
        lab postconditionDefinitionLabel
        lab partialCorrectnessDefinitionLabel
        lab totalCorrectnessDefinitionLabel
        s [hoareLogic', " is a ", theory]
        s ["In ", hoareLogic, ", well-formed ", formula, "e are ", hoareTriple', "s"]
        ma $ htrip p a q
        s ["Here, ", m p, and, m q, " are assertions and ", m a, " is a sequence of instructions for an abstract machine"]
        s [m p, " is called the ", precondition', and, m q, " is called the ", postcondition']
        s ["An ", assertion', " is a ", predicate, " on the set of states"]
        s ["A true sencence in ", hoareLogic, " describes the fact that the program ", m a, " will, started in any machine ", state, " satisfying ", m p, " will, if it terminates, yield a ", state, " satisfying ", m q]
        s ["This is called ",partialCorrectness']
        s ["If a ", hoareTriple, " is partially correct and ", m a, " is guaranteed to ", emph "terminate", " as well, this is called ", totalCorrectness']

hoareTripleNote :: Note
hoareTripleNote = nte $ do
    s ["An employee that needs to implement correct programs for given pre- and postconditions should look for the strongest preconditions and the weakest postconditions"]
    s ["Specifications as such will leave him with the least amount of work to do"]
    s ["The following Hoare specification would give him the best job in the world"]
    ma $ htrip false a p
    s ["Any program ", m a, " is totally correct with respect to this specification"]
    newline
    s ["The second best job in the world would be the following specification"]
    ma $ htrip mempty a true
    s ["Any program ", m a, " is partially with respect to this specification"]
    s ["The only thing the programmer would have to do is to make sure that the program terminates"]

ruleOfConsequenceDefinition :: Note
ruleOfConsequenceDefinition = do
    de $ do
        lab consequenceDefinitionLabel
        s [the, " rule of ", consequence, " is an ", inference, " in ", hoareLogic]
        ma $ linf [htrip p a q, p' ⇒ p, q ⇒ q'] (htrip p' a q')
        s ["A precondition can be replaced with a stronger precondition and a postcondition can be replaced by a weaker postcondition"]
    ex $ ma $ linf [t1, t2, t3] t4
  where
    t1 = htrip (x > 1) (y =:= x + 2) (y > 2)
    t2 = (x > 3) ⇒ (x > 1)
    t3 = (y > 0) ⇒ (y > 2)
    t4 = htrip (x > 3) (y =:= x + 2) (y > 0)
    p' = "P'"
    q' = "Q'"

ruleOfConjunctionDefinition :: Note
ruleOfConjunctionDefinition = do
    de $ do
        lab conjunctionDefinitionLabel
        s [the, " rule of ", conjunction', " is an ", inference, " in ", hoareLogic]
        ma $ linf [htrip p a q, htrip p a r] $ htrip p a (q ∧ r)

    ex $ ma $ linf [t1, t2] t3
  where
    t1 = htrip (true) (x =:= 3) (x > 2)
    t2 = htrip (true) (x =:= 3) (x < 4)
    t3 = htrip (true) (x =:= 3) (x > 2 ∧ x > 4)


sequentialCompositionDefinition :: Note
sequentialCompositionDefinition = do
    de $ do
        lab sequentialCompositionDefinitionLabel
        s [the, " rule of ", sequentialComposition', " is an ", inference, " in ", hoareLogic ]
        ma $ linf [htrip p a q, htrip q b r] $ htrip p (a ؛ b) r
        s ["Instructions can be sequenced as long as their conditions line up"]
    ex $ ma $ linf [t1, t2] t3
  where
    t1 = htrip (x > 0) (x =:= x + 3) (x > 3)
    t2 = htrip (x > 3) (x =:= x + 1) (x > 4)
    t3 = htrip (x > 0) (x =:= x + 3 ؛ x =:= x + 1) (x > 4)

skipDefinition :: Note
skipDefinition = de $ do
    lab skipDefinitionLabel
    s [the, skip', " ", hoareTriple, " is an ", axiomSchema, " in ", hoareLogic]
    ma $ fa p $ htrip p skip p

abortDefinition :: Note
abortDefinition = de $ do
    lab abortDefinitionLabel
    s [the, abort', " ", hoareTriple, " is an ", axiomSchema, " in ", hoareLogic]
    ma $ fa p $ htrip false abort p

substitutionDefinition :: Note
substitutionDefinition = do
    de $ do
        lab substitutionDefinitionLabel
        s [m (repl p e x), " is the expression obtained from ", m p, by, substitution', " of every occurence of ", m x, by, m e]
        s ["Read it as ", dquoted (s [m p, " with ", m e, " instead of ", m x])]

    ex $ dquoted (m $ repl (pars $ y =:= x) z y) <> " " =: " " <> dquoted (m $ z =:= x)
    ex $ dquoted (m $ repl (pars $ y =:= x) (x + 1) x) <> " " =: " " <> dquoted (m $ x =:= x + 1)


assignmentDefinition :: Note
assignmentDefinition = do
    de $ do
        lab assignmentDefinitionLabel
        s ["The ", assignment', " of variables is an ", axiomSchema, " in ", hoareLogic]
        ma $ fa (cs [p,e,x]) $ htrip (repl p e x) (x =:= e) p

    ex $ m $ htrip (y > z - 2) (x =:= x + 1) (y > z - 2)
    ex $ m $ htrip (2 + 2 =: 5) (x =:= x + 1) (2 + 2 =: 5)
    ex $ m $ htrip (y > 0) (x =:= y) (x > 0)
    ex $ do
        m $ htrip (x + 1 > 0) (x =:= x + 1) (x > 0)
        s ["Make sure to read this twice"]
        s ["Notice that it is not at all useful in this context"]
    ex $ do
        s [the , assignment, " ", axiomSchema, " can ", textbf "not", " be used to prove following ", hoareTriple]
        ma $ htrip (x > 0) (x =:= x + 1) (x > 1)
        why

    nte $ do
        s ["There are limits to the assignment axiom schema"]
        s ["It is assumed that the assigned expression is side-effect-free"]
        s ["This always holds in mathematics, but infrequently in real machines"]

forwardAssignmentDefinitionLabel :: Label
forwardAssignmentDefinitionLabel = Label Definition "forward-assignment"

forwardAssignmentDefinition :: Note
forwardAssignmentDefinition = de $ do
    lab forwardAssignmentDefinitionLabel
    s ["There is also a ", quoted "forward version", " of the assignment axiom"]
    ma $ htrip p (x =:= e) (te xo $ (pars $ repl p xo x) ∧ (pars $ x =: repl e xo x))
  where
    x = "x"
    xo = x ^: "old"

freeVariableDefinition :: Note
freeVariableDefinition = de $ do
    lab freeVariableDefinitionLabel
    s ["A variable ", m x, " is said to be a ", freeVariable', " in an expression ", m p, " if ", m p, " doesn't quantify ", m x, " either existentially or universally"]
    newline
    s [m (freevars p), " is the set of all ", freeVariable, "s in an expression ", m p]

modifiesDefinition :: Note
modifiesDefinition = de $ do
    lab modifyDefinitionLabel
    s ["A program ", m a, " is said to ", modify', " a variable ", m x, " if at any point, ", m a, " assigns to ", m x]
    newline
    s [m (modifies a), " is the set of all variables that ", m a, " modifies"]

ruleOfConstancy :: Note
ruleOfConstancy = do
    de $ do
        s [the, term "rule of constancy", " is an ", inference, " in Hoare Logic"]
        s ["Let ", m r, " be an assertion"]
        ma $ linf [htrip p a q, (freevars r) ∩ (modifies a) =§= emptyset] (htrip (p ∧ r) a (q ∧ r))
        s ["This is known as ", dquoted (s ["Whatever ", m a, " doesn't modify, stays the same"])]

    ex $ ma $ e1
    ex $ ma $ e2
    todo "The assignment axiom for arrays"

  where
    e1 = linf [t1, t2] t3
      where
        t1 = htrip (x =: 0) (x =:= x + 1) (x =: 1)
        t2 = (freevars $ y =: 3) ∩ (modifies $ x =:= x + 1) =§= emptyset
        t3 = htrip (x =: 0 ∧ y =: 3) (x =:= x + 1) (x =: 1 ∧ y =: 3)
    e2 = linf [t1, t2] t3
      where
        t1 = htrip (x =: 4) (x =:= sqrt y) (z =: 2)
        t2 = (freevars $ y =: 3) ∩ (modifies $ x =:= sqrt y) =§= emptyset
        t3 = htrip (x =: 4 ∧ y =: 3) (x =:= sqrt y) (z =: 2 ∧ y =: 3)

conditionalRule :: Note
conditionalRule = do
    de $ do
        s [the, term "conditional rule", " is an ", inference, " in Hoare Logic"]
        ma $ linf [htrip (p ∧ c) a q, htrip (p ∧ not c) b q] $ htrip p (ifThenElse c a b) q

    ex $ ma $ e
  where
    e = linf [t1, t2] t3
    t1 = htrip (y > 0 ∧ x > 0) (y =:= y + x) (y > 0)
    t2 = htrip (y > 0 ∧ not (pars $ x > 0)) (y =:= y - x) (y > 0)
    t3 = htrip (y > 0) (ifThenElse (x > 0) (y =:= y + x) (y =:= y - x)) (y > 0)

conditionalRuleGcdProof :: Note
conditionalRuleGcdProof = todo "gcd proof"

loopRuleExampleLabel :: Label
loopRuleExampleLabel = Label Example "loop-rule-example"

loopRuleDefinition :: Note
loopRuleDefinition = do
    de $ do
        lab loopRuleDefinitionLabel
        s [the, loopRule', " is an ", inference, " in Hoare Logic"]
        ma $ linf [htrip p a i, htrip (i ∧ not c) b i] $ htrip p (fromUntilLoop a c b) (i ∧ c)
        s ["The first triple is called the ", term "initiation", and, " the second is called the ", term "consecution", or, term "inductiveness"]
        s ["This rule is also sometimes written as follows"]
        raw "\n"
        prooftree $
            looprule
                (assumption $ m $ htrip p a i)
                (assumption $ m $ htrip (i ∧ not c) b i)
                (assumption $ m $ i ∧ c ⇒ q)
                (m $ htrip p (fromUntilLoop a c b) q)
        raw "\n"
    ex $ do
        lab loopRuleExampleLabel
        ma e
    todo "Loop rule with do while instead of just while."
  where
    e = linf [t1, t2, t3] t4
    t1 = htrip p_ a_ i_
    t2 = htrip (i_ ∧ (pars $ not c_)) b_ i_
    t3 = (pars $ i_ ∧ c_) ⇒ q_
    t4 = htrip p_ (fromUntilLoop a_ c_ b_) q_
    i = "i"
    n = "n"

    p_ = (y > 3 ∧ n > 0)
    q_ = (y > 3 + n)
    a_ = (i =:= 0)
    c_ = (i =: n)
    b_ = seqins [(i =:= i + 1), (y =:= y + 1)]
    i_ = y > 3 + i

termination :: Note
termination = do
    subsection "Termination"
    s ["To show total correctness, rather than just partial correctness, termination must also be proven"]
    s ["Termination is asserted for all but the loop triples if all the antecedents terminate"]

    loopTermination
    terminationProofExample

loopTermination :: Note
loopTermination = de $ do
    s ["To prove the total correctness of a loop triple, we must first prove partial correctness and then loop termination as follows"]
    s ["There must exist a set ", m ss, " with a total ordering ", m ("" <= ""), " such that ", m ss, " has a least element ", m bot, " with respect to ", m ("" <= "")]
    s ["Three more conditions must hold"]

    enumerate $ do
        item $ m $ htrip p a (v >= bot)
        item $ do
            s [m $ brac $ v >= bot, " is an invariant of the loop"]
            ma $ htrip (v >= bot) a (v >= bot)
        item $ do
            s [m v, " decreases with ever iteration"]
            ma $ fa v0 ((v <> "<" <> v0) ⇒ (htrip ((v =: v0) ∧ not c) b (v <> "<" <> v0)))

  where
    ss = "S"
    v = "v"
    v0 = "v'"

terminationProofExample :: Note
terminationProofExample = ex $ do
    s ["This program is totally correct"]
    ma $ htrip p_ l_ q_
    proof $ do
        s ["Partial correctness was already proven in an earlier example", ref loopRuleExampleLabel]
        s ["Only termination is left to prove"]

        s ["Let ", m v, " be the variant of the loop"]
        itemize $ do
            item $ do
                s ["The variant stays positive after initialization"]
                ma $ htrip p_ a_ v_
                toprove
            item $ do
                s [m $ brac v_, " is an invariant of the loop"]
                ma $ htrip v_ b_ v_
                toprove
            item $ do
                s [m v, " decreases with ever iteration"]
                ma $ fa v0 ((v <> "<" <> v0) ⇒ (htrip ((v =: v0) ∧ not c) b (v <> "<" <> v0)))
                toprove
  where
    i = "i"
    n = "n"

    v = pars (n - i)
    v_ = (v >= 0)
    v0 = "v'"
    l_ = (fromUntilLoop a_ c_ b_)
    p_ = (y > 3 ∧ n > 0)
    q_ = (y > 3 + n)
    a_ = (i =:= 0)
    c_ = (i =: n)
    b_ = seqins [(i =:= i + 1), (y =:= y + 1)]

exampleProof :: Note
exampleProof = ex $ do
    s ["The following ", hoareTriple, is, true]
    ma $ t_

    proof $ do
        prooftree $ do
            seqcomp
                (
                conseq2
                    (assignmentAs $ m $ htrip p_' a1_ q_)
                    (elemmath $ m $ p_ ⇒ p_')
                    (m $ htrip p_ a1_ q_)
                )
                (skipAs $ m $ htrip q_ a2_ q_)
                (m t_)


  where
    t_ = htrip p_ a_ q_
    p_ = x > 0
    p_' = x + 1 > 1
    a_ = a1_ ؛ a2_
    a1_ = x =:= x + 1
    a2_ = skip
    q_ = x > 1


softwareVerificationAxiomaticSemanticsSlides :: Reference
softwareVerificationAxiomaticSemanticsSlides = Reference lectureSlides "software-verification-axiomatic-semantics-part1"
  [
    ("author", "Bertrand Meyer")
  , ("title", "Lecture 2: Axiomatic Semantics")
  , ("year", "2015")
  , ("month", "September")
  , ("note", "Lecture Slides")
  ]
