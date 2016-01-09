module Logic.HoareLogic.ExamQuestion2014 where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Logic.HoareLogic.Macro
import           Logic.HoareLogic.Terms
import           Logic.PropositionalLogic.Macro

examQuestion2014 :: Note
examQuestion2014 = ex $ do
    examq eth "Software Verification" "December 2014"
    s ["The following ", hoareTriple, " represents a partially correct program"]
    ma ht_

    proof $ do
        s ["The tree for this proof would be large enough to fill an A2 or even an A1 page and must therefore be broken down"]

        s ["The first thing to do for a loop like this, is to find an invariant of the loop"]
        s ["It needs to be strong enough to, in conjunction with the guard, imply the postcondition"]
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
                        let figlabel = MkLabel Figure "fig:consequence-in-this-exam-thingy1"
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
                        let figlabel = MkLabel Figure "fig:consequence-in-this-exam-thingy2"
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
                framed $ ma $ htrip_ (centeredBelowEachOther [inv_, "" ∧ ncond_]) body_ inv_
                s ["Here we use the rule of sequenctial composition to split this up into two parts"]
                s ["We'll use the following inbetween-assertion"]
                ma inb_
                enumerate $ do
                    item $ do
                        noindent
                        framed $ ma $ htrip_ (centeredBelowEachOther [inv_, "" ∧ ncond_]) body1_ inb_
                        s ["First we apply the conditional rule to this if-then-else construction to split it up into two parts"]
                        enumerate $ do
                            item $ do
                                noindent
                                framed $ ma $ htrip_ (centeredBelowEachOther [inv_, "" ∧ ncond_, "" ∧ icond_]) ibody_ inb_
                                s ["We'll first have to rewrite the postcondition to get some concretisation of the universal quantifier"]
                                let rewr_ = centeredBelowEachOther
                                        [
                                          inb_
                                        , "" ∧ sep_
                                        ]
                                let rewr_' = centeredBelowEachOther
                                        [
                                          inb_
                                        , "" ∧ sep_'
                                        ]
                                ma $ htrip_ (centeredBelowEachOther [inv_, "" ∧ ncond_, "" ∧ icond_]) ibody_ rewr_

                                s ["The assignment axiom then gets us the following"]
                                prooftree $ assignmentAs $ m $ htrip_ rewr_' ibody_ rewr_
                                s ["Now we only have to prove that the precondition of the original triple implies the precondition of the second and apply the rule of consequence"]
                                ma $ centeredBelowEachOther $
                                    [
                                    inv_
                                    , "" ∧ ncond_
                                    , "" ∧ icond_
                                    , "" ⇒ ""
                                    , rewr_'
                                    ]
                                s $ ["The first element in the conjunction at the conclusion can be omitted because they are in the hypothesis"]
                                ma $ centeredBelowEachOther $
                                    [
                                    inv_
                                    , "" ∧ ncond_
                                    , "" ∧ icond_
                                    , "" ⇒ ""
                                    , inb2_
                                    , sep_'
                                    ]
                                s ["We can intuitively see that in the conjunction of the precondition, the second an fourth elements imply the first element of the postcondition .."]
                                ma $ centeredBelowEachOther [inv2_, "" ∧ icond_ , "" ⇒ inb2_]
                                s ["... and the fourth elemnt implies the second element of the postcondition by itself"]
                                ma $ icond_ ⇒ sep_'
                                todo "Can this be more rigorous?"
                                let figlabel = MkLabel Figure "fig:consequence-in-this-exam-thingy2b"
                                s ["The rule of consequence can now be used to prove this triple", ref figlabel]
                                sidewaysFigure $ do
                                    prooftree $ do
                                        conseq2
                                            (assumption $ m $ htrip_ rewr_' ibody_ rewr_)
                                            (assumption $ m $ centeredBelowEachOther [inv_ , "" ∧ ncond_, "" ∧ icond_, "" ⇒ "", rewr_'])
                                            (m $ htrip_ (centeredBelowEachOther [inv_, "" ∧ ncond_, "" ∧ icond_]) ibody_ inb_)
                                    lab figlabel
                                    caption "Application of the rule of consequence"
                            item $ do
                                noindent
                                let preP = centeredBelowEachOther [inv_, "" ∧ ncond_, "" ∧ nicond_]
                                framed $ ma $ htrip_ preP skip inb_
                                s ["To prove this triple, we have to prove that the precondition implies the postcondition and then apply the rule of consequence to the skip axiom schema"]
                                s ["The first part of the postcondition can be imediately asserted as it is part of a conjunction in the precondition"]
                                ma $ centeredBelowEachOther [inv_, "" ∧ ncond_, "" ∧ nicond_, "" ⇒ inb1_]
                                s ["Left to prove is now the following implication"]
                                ma $ centeredBelowEachOther [inv_, "" ∧ ncond_, "" ∧ nicond_, "" ⇒ inb2_]
                                s ["The only difference is in the hypothesis of the second implication"]
                                s ["If we strip the unnecessary as follows, it becomes intuitively clear that this implication holds"]
                                ma $ centeredBelowEachOther [inv2_, "" ∧ nicond_, "" ⇒ inb2_]
                                todo "can this be done more rigorously?"
                                let figlabel = MkLabel Figure "fig:consequence-in-this-exam-thingy2c"
                                s ["The rule of consequence can now be used to prove this triple", ref figlabel]
                                sidewaysFigure $ do
                                    prooftree $ do
                                        conseq2
                                            (assumption $ m $ htrip_ preP skip preP)
                                            (assumption $ m $ centeredBelowEachOther [preP, "" ⇒ "", inb_])
                                            (m $ htrip_ preP skip inb_)
                                    lab figlabel
                                    caption "Application of the rule of consequence"

                    item $ do
                        noindent
                        framed $ ma $ htrip_ inb_ body2_ inv_
                        let figlabel = MkLabel Figure "fig:consequence-in-this-exam-thingy3"
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
    ht_     = htrip_ p_ a_ q_
    p_      = (pars $ n > 0) ∧ (pars $ (fa i $ (pars $ 0 <= i < n) ⇒ (pars $ a ! i =: b ! i =: 0)))
    a_      = fromUntilLoop_ init_ cond_ body_
    q_      = fa i $ (pars $ (pars $ 0 <= i < n) ∧ (pars $ i `mod` 3 =: 0)) ⇒ (pars $ b ! i =: 1)
    init_   = commS "," <> (k =:= 0)
    cond_   = commS "," <> (k =: n)
    ncond_  = commS "," <> (k /=: n)
    inv_    = centeredBelowEachOther [inv1_, "" ∧ inv2_]
    inv1_   = fa i $ (pars $ (pars $ 0 <= i < k) ⇒ (a ! i =: 0))
    inv1_'  = fa i $ (pars $ (pars $ 0 <= i < 0) ⇒ (a ! i =: 0))
    inv2_   = fa i $ (pars $ (pars $ 0 <= i < k) ∧ (pars $ i `mod` 3 =: 0)) ⇒ (pars $ b ! i =: 1)
    inv2_'  = fa i $ (pars $ (pars $ 0 <= i < 0) ∧ (pars $ i `mod` 3 =: 0)) ⇒ (pars $ b ! i =: 1)
    body_   = seqins [body1_, body2_]
    body1_  = ifThen_ icond_ ibody_
    body2_  = commS "," <> (k =:= k + 1)
    icond_  = commS "," <> (k `mod` 3 =: 0)
    nicond_ = commS "," <> (k `mod` 3 /=: 0)
    ibody_  = (b ! k =:= a ! k + 1)
    inb_    = centeredBelowEachOther [inb1_, inb2_]
    inb1_   = inv1_
    inb2_   = inv2e_
    inv2e_  = fa i $ (pars $ (pars $ 0 <= i < k + 1) ∧ (pars $ i `mod` 3 =: 0)) ⇒ (pars $ b ! i =: 1)
    sep_    = ((pars $ k `mod` 3 =: 0) ⇒ b ! k =: 1)
    sep_'    = ((pars $ k `mod` 3 =: 0) ⇒ a ! k + 1 =: 1)

    a = "a"
    b = "b"
    p = "P"
    q = "Q"
    i = "i"
    n = "n"
    k = "k"

