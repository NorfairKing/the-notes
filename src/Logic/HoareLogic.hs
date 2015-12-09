module Logic.HoareLogic where

import           Notes

import           Logic.AbstractLogic    (axiomSchema, formula, inference,
                                         theory)
import           Sets.Basics            (predicate)

import           Logic.HoareLogic.Macro
import           Relations.Orders.Macro

makeDefs [
      "Hoare logic"
    , "state"
    , "instruction"
    , "Hoare triple"
    , "precondition"
    , "postcondition"
    , "assertion"
    , "partial correctness"
    , "total correctness"

    , "consequence"
    , "conjunction"
    , "sequential composition"

    , "skip"
    , "abort"

    , "substitution"
    , "assignment"
    , "loop rule"

    , "free variable"
    , "modify"
    ]

hoareLogicS :: Notes
hoareLogicS = notesPart "hoare-logic" $ do
    section "Hoare Logic"
    hoareLogicDefinition
    hoareTripleNote

    ruleOfConsequenceDefinition
    ruleOfConjunctionDefinition
    sequentialCompositionDefinition

    skipDefinition
    abortDefinition
    substitutionDefinition
    assignmentDefinition
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

hoareLogicDefinition :: Note
hoareLogicDefinition = do
    s [hoareLogic', " is used to reason about imperative computer programs in abstract machines that have a ", state]
    s ["A ",state', " is an assignment of values to abstract symbols"]
    s ["An ", instruction', " in such an abstract machine is a procedure of modifying that ", state]
    de $ do
        lab hoareLogicDefinitionLabel
        lab stateDefinitionLabel
        lab instructionDefinitionLabel
        lab hoareTripleDefinitionLabel
        lab preconditionDefinitionLabel
        lab postconditionDefinitionLabel
        lab assertionDefinitionLabel
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
        s [m (lrepl p e x), " is the expression obtained from ", m p, by, substitution', " of every occurence of ", m x, by, m e]
        s ["Read it as ", dquoted (s [m p, " with ", m e, " instead of ", m x])]

    ex $ dquoted (m $ lrepl (pars $ y =:= x) z y) <> " " =: " " <> dquoted (m $ z =:= x)
    ex $ dquoted (m $ lrepl (pars $ y =:= x) (x + 1) x) <> " " =: " " <> dquoted (m $ x =:= x + 1)


assignmentDefinition :: Note
assignmentDefinition = do
    de $ do
        lab assignmentDefinitionLabel
        s ["The ", assignment', " of variables is an ", axiomSchema, " in ", hoareLogic]
        ma $ fa (cs [p,e,x]) $ htrip (lrepl p e x) (x =:= e) p

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

examQuestion2014 :: Note
examQuestion2014 = ex $ do
    examq "Software Verification" "August 2014"
    s ["The following ", hoareTriple, " represents a partially correct program"]
    ma ht_

    proof $ do
        s ["The first thing to do for a loop like this, is to find an invariant of the loop"]
        s ["A good first suggestion could be the following"]
        ma $ "Inv" =: inv_
        s ["Now that we have a loop invariant, we can use the ", loopRule_, " to prove this Hoare triple"]
        s ["This means that we now have three smaller parts to prove"]
        enumerate $ do
            item $ do
                noindent
                framed $ ma $ htrip_ p_ init_ inv_
                s ["The rule of conjunction allows us to split this up again"]
                enumerate $ do
                    item $ do
                        noindent
                        framed $ ma $ htrip_ p_ init_ inv1_
                        s ["We will use the assignment axiom schema to prove this triple"]
                        s ["The following hoare triple is an instance of the assignment axiom schema"]
                        prooftree $ assignmentAs $ m $ htrip_ inv1_' init_ inv1_
                        s ["It's precondition can be rewritten as follows"]
                        ma $
                            inv1_'
                            ⇔ fa i (pars $ false ⇒ (a ! i =: 0))
                            ⇔ true
                        s ["Thus we have the following triple"]
                        ma $ htrip true init_ inv1_
                        let figlabel = figlab "fig:consequence-in-this-exam-thingy1"
                        s $ ["Because anything implies true, we can use the rule of consequence", ref figlabel]
                        sidewaysFigure $ do
                            prooftree $ do
                                conseq2
                                    (assumption $ m $ htrip_ true init_ inv1_)
                                    (assumption $ m $ p_ ⇒ true)
                                    (m $ htrip_ p_ init_ inv1_)
                            lab figlabel
                            caption "Application of the rule of consequence"

                    item $ do
                        noindent
                        framed $ ma $ htrip_ p_ init_ inv2_
                        s ["Analogous to the previous point, the assignment axiom schema gives us this triple"]
                        prooftree $ assignmentAs $ m $ htrip_ inv2_' init_ inv2_
                        s ["The precondition can again be rewritten as ", m true]
                        align_
                            [
                                    inv2_'
                                  & "" ⇔ fa i ((pars $ false ∧ (pars $ i `mod` 3 =: 0)) ⇒ (pars $ b ! i =: 1))
                            , " " & " " ⇔ fa i (pars $ false ⇒ (pars $ b ! i =: 1))
                            , " " & " " ⇔ true
                            ]
                        s ["This gives us the following triple"]
                        ma $ htrip true init_ inv2_
                        let figlabel = figlab "fig:consequence-in-this-exam-thingy2"
                        s ["Once more we use the rule of consequence to use this triple to proof the given triple", ref figlabel]
                        sidewaysFigure $ do
                            prooftree $ do
                                conseq2
                                    (assumption $ m $ htrip_ true init_ inv2_)
                                    (assumption $ m $ p_ ⇒ true)
                                    (m $ htrip_ p_ init_ inv2_)
                            lab figlabel
                            caption "Application of the rule of consequence"

            item $ do
                noindent
                framed $ ma $ htrip_ (inv_ ∧ ncond_) body_ inv_
                s ["Here we use the rule of sequenctial composition to split this up into two parts"]
                s ["We'll use the following inbetween-assertion"]
                ma inb_
                enumerate $ do
                    item $ do
                        noindent
                        framed $ ma $ htrip_ (inv_ ∧ ncond_) body1_ inb_
                        s ["First we apply the conditional rule to this if-then-else construction to split it up into two parts"]
                        enumerate $ do
                            item $ do
                                noindent
                                framed $ ma $ htrip_ (inv_ ∧ ncond_ ∧ icond_) ibody_ inb_
                                todo "I'm stuck here"
                            item $ do
                                noindent
                                framed $ ma $ htrip_ (inv_ ∧ ncond_ ∧ nicond_) skip inb_
                                s ["To prove this triple, we have to prove that the precondition implies the postcondition and then apply the rule of consequence"]
                                s ["The first part of the postcondition can be imediately asserted as it is part of a conjunction in the precondition"]
                                ma $ centeredBelowEachOther [inv_, "" ∧ ncond_, "" ∧ nicond_, "" ⇒ inb1_]
                                s ["Left to prove is now the following implication"]
                                ma $ centeredBelowEachOther [inv_, "" ∧ ncond_, "" ∧ nicond_, "" ⇒ inb2_]
                                s ["The only difference is in the hypothesis of the second implication"]
                                s ["If we strip the unnecessary as follows, it becomes intuitively clear that this implication holds"]
                                ma $ centeredBelowEachOther [inv2_, "" ∧ nicond_, "" ⇒ inb2_]
                                todo "can this be done more rigorously?"
                                todo "apply the rule of consequence"

                    item $ do
                        noindent
                        framed $ ma $ htrip_ inb_ body2_ inv_
                        let figlabel = figlab "fig:consequence-in-this-exam-thingy3"
                        s ["First we'll use the rule of constancy to get rid of the first part of each condition", ref figlabel]
                        sidewaysFigure $ do
                            prooftree $ do
                                constancy
                                    (assumption $ m $ htrip_ inv2e_ body2_ inv2_)
                                    (assumption $ m $ centeredBelowEachOther
                                        [freevars inv1_, "" ∩ "", modifies body2_, "" =§= emptyset])
                                    (m $ htrip_ inb_ body2_ inv_)
                            lab figlabel
                            caption "Application of the rule of constancy"
                        s ["This leaves us with the following triple to prove"]
                        ma $ htrip_ inv2e_ body2_ inv2_
                        s ["This is an instantiation of the assignment axiom schema"]

            item $ do
                noindent
                framed $ ma $ centeredBelowEachOther [inv_, "" ∧ commS "," <> cond_, " " ⇒ q_]
                s ["Simply replacing ", m k, by, m n, " in the hypothesis, gets us this implication"]
                ma $ centeredBelowEachOther [inv1_ ∧ q_, " " ⇒ q_]
                s ["This is of the form ", m (p ∧ q ⇒ q), " and is therefore clearly true"]

  where
    ht_ = htrip_ p_ a_ q_
    p_ = (pars $ n > 0) ∧ (pars $ (fa i $ (pars $ 0 <= i < n) ⇒ (pars $ a ! i =: b ! i =: 0)))
    a_ = fromUntilLoop_ init_ cond_ body_
    q_ = fa i $ (pars $ (pars $ 0 <= i < n) ∧ (pars $ i `mod` 3 =: 0)) ⇒ (pars $ b ! i =: 1)
    init_ = commS "," <> (k =:= 0)
    cond_ = commS "," <> (k =: n)
    ncond_ = commS "," <> (k /=: n)
    inv_ = centeredBelowEachOther [inv1_, "" ∧ inv2_]
    inv1_ = fa i $ (pars $ (pars $ 0 <= i < k) ⇒ (a ! i =: 0))
    inv1_' = fa i $ (pars $ (pars $ 0 <= i < 0) ⇒ (a ! i =: 0))
    inv2_ = fa i $ (pars $ (pars $ 0 <= i < k) ∧ (pars $ i `mod` 3 =: 0)) ⇒ (pars $ b ! i =: 1)
    inv2_' = fa i $ (pars $ (pars $ 0 <= i < 0) ∧ (pars $ i `mod` 3 =: 0)) ⇒ (pars $ b ! i =: 1)
    body_ = seqins [body1_, body2_]
    body1_ = ifThen_ icond_ ibody_
    body2_ = commS "," <> (k =:= k + 1)
    icond_ = commS "," <> (k `mod` 3 =: 0)
    nicond_ = commS "," <> (k `mod` 3 /=: 0)
    ibody_ = (b ! k =:= a ! k + 1)
    inb_ = centeredBelowEachOther [inb1_, inb2_]
    inb1_ = inv1_
    inb2_ = inv2e_
    inv2e_ = fa i $ (pars $ (pars $ 0 <= i < k + 1) ∧ (pars $ i `mod` 3 =: 0)) ⇒ (pars $ b ! i =: 1)

    a = "a"
    b = "b"
    i = "i"
    n = "n"
    k = "k"






