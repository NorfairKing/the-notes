module FormalMethods.Main where

import           Notes                          hiding (constant, cyclic,
                                                 inverse)

import           Cryptography.Terms             hiding (signature, signature',
                                                 signatureDefinitionLabel)
import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Inverse.Macro
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Relations.Equivalence.Macro
import           Relations.Equivalence.Terms
import           Sets.Basics.Terms

import           FormalMethods.Macro
import           FormalMethods.Terms

formalMethods :: Note
formalMethods = chapter "Formal Methods" $ do
    signatureDefinition
    constantDefinition
    signatureArityNote
    peanoExampleSig
    termAlgebraDefinition
    peanoExampleAlgebra
    equationDefinition
    peanoEquationsExample
    equationalTheoryDefinition
    orientedEquationDefinition
    cryptographicMessagesTermAlgebra
    cryptographicMessagesEquations
    freeTermAlgebraDefinition
    semanticEqualityDefinition
    quotientTermAlgebraDefinition
    substitutionDefinition
    substitutionExamples
    compositionSubstitution
    positionDefinition
    subtermExamples
    matchesDefinition
    matchesExamples
    subtermReplacement
    subtermReplacementExamples
    applicationDefinition
    applicationExamples
    unifiableDefinition
    unifiableExamples
    mostGeneralUnifier
    equalityStepDefinition
    equalityRelationDefinition
    equalityProofDefinition
    equalityProofExamples
    infiniteComputationsDefinition
    terminatingDefinition
    terminatingExamples
    reachingNotation
    confluenceDefinition
    confluenceExamples


signatureDefinition :: Note
signatureDefinition = de $ do
    lab signatureDefinitionLabel
    lab arityDefinitionLabel
    s ["A", signature', m sig_, "is a", set, "of so-called", function, "symbols, each with an", arity']

constantDefinition :: Note
constantDefinition = de $ do
    lab constantDefinitionLabel
    s ["A", constant', "is an element of a", signature, "with arity", m 0]

signatureArityNote :: Note
signatureArityNote = nte $ s ["For a", function, "symbol with arity", m 2, "the infix notation is sometimes used"]

peanoExampleSig :: Note
peanoExampleSig = ex $ do
    s ["Let", m $ sig_ =: setofs [0, "s", "+"], "where", m 0, "is a", constant, m "s", "has", arity, m 1, "and", m "+", "has", arity, m 2]
    s ["In this setting of the Peano numbers,", m sig_, "is a", signature]

termAlgebraDefinition :: Note
termAlgebraDefinition = de $ do
    lab variableDefinitionLabel
    lab termAlgebraDefinitionLabel
    lab termDefinitionLabel
    s ["Let", m sig_, "be a", signature, and, m vars_, "a", set, "of", variables', "such that", m $ sig_ ∩ vars_, "is empty"]
    s ["Define the", termAlgebra', m ta_, "over", m sig_, "as the", smallest, set, "as follows"]
    itemize $ do
        item $ m $ vars_ ⊆ ta_
        let t = "t"
            t1 = t !: 1
            t2 = t !: 2
            i = "i"
            ti = t !: i
            f = "f"
        item $ m $ fa (list t1 t2 ti ∈ ta_) $ fa (f ∈ sig_) $ fn f (list t1 t2 ti) ∈ ta_
    s [the, elements, "of", m ta_, "are called", terms']

peanoExampleAlgebra :: Note
peanoExampleAlgebra = ex $ do
    let succ = "succ"
        x = "X"
        pta = ta (setofs [0, succ, x]) (setof x)
    s ["The following are elements of", m pta]
    itemize $ do
        item $ m $ fn succ 0
        item $ m $ fn succ (fn succ 0) + fn succ x
    s ["However, ", m $ "" + fn succ 0 + "", "is not an", element, "of", m pta]

equationDefinition :: Note
equationDefinition = de $ do
    lab equationDefinitionLabel
    s ["Let", m ta_, "be a", termAlgebra]
    let t = "t"
        t' = "t'"
    s ["An", equation', "is a pair of", m terms', m (tuple t t') <> ", written", m $ t =: t']

peanoEquationsExample :: Note
peanoEquationsExample = ex $ do
    s [the, equations, m eqs_, "defining the Peano natural numbers are the following"]
    let succ = fn "succ"
    itemize $ do
        let x = "X"
        item $ m $ x + 0 =: x
        let y = "Y"
        item $ m $ x + succ y =: succ (x + y)


equationalTheoryDefinition :: Note
equationalTheoryDefinition = de $ do
    s ["Let", m sig_, "be a", signature, "and", m eqs_, "a set of", equations']
    s [m et_, "is called an", equationalTheory']

orientedEquationDefinition :: Note
orientedEquationDefinition = de $ do
    lab ruleDefinitionLabel
    let t = "t"
        t' = "t'"
    s ["An", equation, m $ t =: t', "can be oriented"]
    s ["If it is oriented left, it is written as", m $ rr t t']
    s ["If it is oriented right, it is written as", m $ lr t t']
    s ["An oriented", equation, "is called a", rule']

equationalDerivationDefinition :: Note
equationalDerivationDefinition = de $ do
    lab equationalDerivationDefinitionLabel
    s ["Let", m et_, "be an", equationalTheory]
    s ["An", equationalDerivation', "in", m et_, "is a list of", terms, "such that every pair of two successive", terms, "is an", equation, "in", m eqs_]

cryptographicMessagesTermAlgebra :: Note
cryptographicMessagesTermAlgebra = de $ do
    s [the, termAlgebra, "of", "cryptographic messages", "is defined as follows"]
    s ["Let the following be a", signature]
    ma $ sig_ =: ags_ ∪ frsh_ ∪ fncs_ ∪ setofs [pair cdot_ cdot_, pk cdot_, aenc cdot_ cdot_, senc cdot_ cdot_]
    itemize $ do
        item $ s [m vars_ <> ":", the, set, "of", variables]
        item $ s [m ags_  <> ":", the, set, "of", agents]
        item $ s [m fncs_ <> ":", the, set, "of", functions]
        let t = "t"
            t1 = t !: 1
            t2 = t !: 2
        item $ s [m $ pair t1 t2 <> ":", "pairing"]
        item $ s [m $ pk t <> ":", publicKey]
        item $ s [m $ aenc t1 t2 <> ":", "asymmetric encryption"]
        item $ s [m $ senc t1 t2 <> ":", "symmetric encryption"]
    s ["In this", termAlgebra, "every term is called a", message]

cryptographicMessagesEquations :: Note
cryptographicMessagesEquations = de $ do
    s [the, equationalTheory, "of", "cryptographic messages", "contains the following", equations]
    itemize $ do
        let mesg = "M"
            k = "K"
        item $ m $ aenc (aenc mesg k) (inv k) =: mesg
        item $ m $ inv (inv k) =: k
        item $ m $ senc (senc mesg k) k =: mesg
        let x = "X"
            y = "Y"
            b = "B"
        item $ m $ exp_ (exp_ b x) y =: exp_ (exp_ b y) x

freeTermAlgebraDefinition :: Note
freeTermAlgebraDefinition = de $ do
    s [the, freeTermAlgebra', "over a given", termAlgebra, m ta_, "is the", termAlgebra, "in which every", term, "is interpreted as its syntactic representation"]
    s ["We define the", freeEquationalTheory', "over it with", equations, "as follows"]
    let t = "t"
        t1 = t !: 1
        t2 = t !: 2
    ma $ t1 =: t2 <> text " if and only if " <> t1 =!= t2

semanticEqualityDefinition :: Note
semanticEqualityDefinition = nte $ do
    let t = "t"
    s ["A", set, "of", equations, m eqs_, "induces a congruence relation", m eqr_, "on", terms, "and thus the equivalence class", m $ eqcl eqr_ t, "of a", term, m t, "modulo", m eqs_]
    s ["This congruence relation is called", defineTerm "semantic equality"]

quotientTermAlgebraDefinition :: Note
quotientTermAlgebraDefinition = de $ do
    s ["Let", m sig_, "be a", signature <> ", ", m vars_, asetof, variables, and, m eqs_, asetof, equations]
    s [the, quotientTermAlgebra', m $ eqr_ `eqcls` ta sig_ vars_, "interprets each", term, "by its own", equivalenceClass]

substitutionDefinition :: Note
substitutionDefinition = de $ do
    lab substitutionDefinitionLabel
    s ["Let", m sig_, "be a", signature, and, m vars_, asetof, variables]
    let sub = fn subs_
        x = "x"
    s ["A", substitution', m subs_, "is a", function, m $ fun subs_ vars_ ta_, "where", m $ sub x, "is different from", m x, "for finitely many", m $ x ∈ vars_]

    s ["We write substitutions in postfix notation and homomorphically extend them to a mapping", m $ fun subs_ ta_ ta_, "on", terms, "as follows"]
    let t = "t"
        t1 = t !: 1
        t2 = t !: 2
        n = "n"
        tn = t !: n
        f = "f"
    ma $ sb subs_ (fn f $ list t1 t2 tn) =: fn f (list (sb_ t1) (sb_ t2) (sb_ tn))

substitutionExamples :: Note
substitutionExamples = do
    ex $ do
        let x = "X"
            mesg = "M"
            k = "K"
        s ["Given a", substitution, m $ subs_ =: setof (x <> mapsto <> senc mesg k), "and the term", m $ pair x k, "we can apply the", substitution, "to get the following", term]
        ma $ sb_ (pair x k) =: pair (senc mesg k) k

compositionSubstitution :: Note
compositionSubstitution = thm $ do
    s ["The composition of", substitutions, "is again a", substitution]
    toprove

positionDefinition :: Note
positionDefinition = de $ do
    lab positionDefinitionLabel
    lab subtermDefinitionLabel
    s ["A", position', "is a list of natural numbers"]
    let t = "t"
        p = pos_
    s ["Given a position", m p <> ",", the, subterm, m $ t |. p, "of a", term, m t, "at", position, m p, "is defined as follows"]
    let t = "t"
        t1 = t !: 1
        t2 = t !: 2
        i = "i"
        ti = t !: i
        n = "n"
        tn = t !: n
    itemize $ do
        item $ m $ t |. nil === t
        item $ do
            let f = "f"
            s ["Let", m t, "be a", term, "of the form", m $ t =: fn f (list t1 t2 tn), "for", m $ f ∈ sig_, and, m $ 1 <= i <= n]
            let q = "q"
            ma $ t |. (cns i q) === ti |. q


subtermExamples :: Note
subtermExamples = ex $ do
    let t = "t"
        mesg = "M"
        k = "K"
    s ["For the", term, m $ t =: sdec_ (senc_ mesg k) k, "there are five subterms"]

    itemize $ do
        item $ m $ t |. nil =: t
        item $ m $ t |. sing 1 =: senc_ mesg k
        item $ m $ t |. listofs [1, 1] =: mesg
        item $ m $ t |. listofs [1, 2] =: k
        item $ m $ t |. sing 2 =: k

matchesDefinition :: Note
matchesDefinition = de $ do
    lab matchesDefinitionLabel
    lab matchingSubstitutionDefinitionLabel
    let t = "t"
        l = "l"
    s ["A", term, m t, matches', "another", term, m l, "if there is a", subterm, "of", m $ t |. pos_, "such that there is a", substitution, m subs_, "so that", m $ t |. pos_ =: sb_ l]
    s ["We call this", substitution, "the", matchingSubstitution']

matchesExamples :: Note
matchesExamples = do
    ex $ do
        let t = "t"
            mesg = "M"
            k = "K"
        s ["Let", m $ t =: sdec_ (senc_ mesg k) k, "be a", term]
        itemize $ do
            item $ s [m $ senc_ mesg k, matches, m t, "at", position, m $ sing 1, "with the identity", matchingSubstitution]
            let x = "X"
            item $ s [m x, matches, m t, "at", position, m $ sing 1, "with", m $ funcomp [(x, senc_ mesg k)], "as", matchingSubstitution]
            item $ s [m x, matches, m t, "at", position, m nil, "with", m $ funcomp [(x, t)], "as", matchingSubstitution]
            item $ s [m $ sdec_ x k, matches, m t, "at", position, m nil, "with", m $ funcomp [(x, senc_ mesg k)], "as", matchingSubstitution]
            item $ s [m $ sdec_ (senc_ mesg x) x, matches, m t, "at", position, m nil, "with", m $ funcomp [(x, k)], "as", matchingSubstitution]
            let y = "Y"
            item $ s [m $ pair x y, "does not match", m t, "anywhere"]


subtermReplacement :: Note
subtermReplacement = de $ do
    let t = "t"
        r = "r"
        p = pos_
    s ["Let", m t, "be a", term, and, m p, "a", position, "with", matchingSubstitution, m subs_]
    s ["Let", m r, "be another", term]
    s ["We denote", m t, "with the subterm at", position, m p, "replaced by", m r, "as", m $ trepl t r p]

subtermReplacementExamples :: Note
subtermReplacementExamples = do
    ex $ do
        let t = "t"
            mesg = "M"
            k = "K"
            r = "r"
            x = "X"
            y = "Y"
        s ["Let", m $ t =: sdec_ (senc_ mesg k) k, and, m $ r =: pair x y, "be", terms]
        itemize $ do
            item $ m $ trepl t r (sing 1) =: sdec_ (pair x y) k
            item $ m $ trepl t y (listofs [1, 2]) =: sdec_ (senc_ mesg y) k
            item $ m $ trepl t r nil =: r

applicationDefinition :: Note
applicationDefinition = de $ do
    lab applicableDefinitionLabel
    lab applicationDefinitionLabel
    let l = "l"
        t = "t"
        r = "r"
        p = pos_
    s ["A", rule, m $ rr l r, "is", applicable', "on a", term, m t, "when", m t, "matches", m l]
    s [the, "result of applying such a", rule, "is the", term, m $ trepl t (sb_ r) p, "where", m subs_, "is the", matchingSubstitution]

applicationExamples :: Note
applicationExamples = do
    ex $ do
        let t = "t"
            mesg = "M"
            k = "K"
        s ["Let", m $ t =: sdec_ (senc_ mesg k) k, "be a", term]
        let x = "X"
        s [m x, matches, m t, "at", position, m $ sing 1, "with", m $ funcomp [(x, senc_ mesg k)], "as", matchingSubstitution]
        let y = "Y"
            z = "Z"
        s ["Let", m $ rr x $ pair y z, "be a", rule]
        s ["This", rule, "is", applicable, "to", m t, "because", m x, "matches", m t]
        s ["The result of the application is", m $ sdec_ (pair y z) k]
    ex $ do
        let t = "t"
            a = "A"
            b = "B"
        s ["Let", m $ t =: pair a b, "be a", term]
        let x = "X"
        s [m $ pair x b, matches, m t, "at", position, m nil, "with", matchingSubstitution, m $ funcomp [(x, a)]]
        s [the, rule, m $ rr (pair x b) (pair b x), "is", applicable, "to", m t, "and the result is", m $ pair b x]

unifiableDefinition :: Note
unifiableDefinition = de $ do
    lab unifiableDefinitionLabel
    lab unifierDefinitionLabel
    lab unifyDefinitionLabel
    let t = "t"
        t1 = t !: 1
        t2 = t !: 2
    s ["We say that an", equation, m $ t1 =?= t2, "is", unifiable, "in an", equationalTheory, m et_, "for", m $ cs [t1, t2] ∈ ta_, "if there is a", substitution, m subs_, "such that", m $ sb_ t1 `eq_` sb_ t2, "holds"]
    s ["We then call", m subs_, "a", unifier]

unifiableExamples :: Note
unifiableExamples = do
    let f_ = "f"
        f = fn2 f_
        h_ = "h"
        h = fn h_
        a = "a"
        b = "b"
        x = "X"
        y = "Y"
        z = "Z"
        ta_ = ta (setofs [f_, h_, a, b]) (setofs [x, y, z])
    ex $ do
        s ["In the", freeEquationalTheory, "over", m ta_, "the following statements are true"]
        itemize $ do
            item $ s [m $ f x y =?= f (h a) x, "is", unifiable, "by the", substitution, m $ funcomp [(x, h a), (y, x)]]
            item $ s [m $ f x y =?= f (h x) x, "is not", unifiable, "because", m x, and, m $ h x, "can never", unify]
            item $ s [m $ f x b =?= f (h y) z, "is", unifiable, "by the", substitution, m $ funcomp [(x, h y), (z, b)]]
            item $ s [m $ f x x =?= f (h y) y, "is not", unifiable]


mostGeneralUnifier :: Note
mostGeneralUnifier = de $ do
    s [the, defineTerm "most general unifier", "TODO"]

equalityStepDefinition :: Note
equalityStepDefinition = de $ do
    lab equalityStepDefinitionLabel
    let u = "u"
        v = "v"
    s ["Let", m et_, "be an", equationalTheory, "and let", m u, and, m v, "be", terms, "in", m ta_]
    s ["If either", m $ rr u v, or, m $ lr u v, "is in", m eqs_, "then", m $ u <--> v, "is said to be an", m eqs_ <> "-" <> equalityStep']

equalityRelationDefinition :: Note
equalityRelationDefinition = de $ do
    lab equalityRelationDefinitionLabel
    s ["Let", m et_, "be an", equationalTheory]
    s [the, "transitive-reflexive closure", "of", m $ "" <--> "", "is the", m eqs_ <> "-" <> equalityRelation', m eqr_]
    todo "define transitive reflexive closure, or just closures in general"

equalityProofDefinition :: Note
equalityProofDefinition = de $ do
    lab equalityProofDefinitionLabel
    s ["Let", m et_, "be an", equationalTheory]
    let t = "t"
        t0 = t !: 0
        t1 = t !: 1
        n = "n"
        tn = t !: n
    s ["A list of", equalitySteps, m $ t0 <--> t1 <--> dotsc <--> tn <> ", witnessing", m n <> "-" <> equalityStep, "equality of", m t0, and, m tn, "is called an", equalityProof']

equalityProofExamples :: Note
equalityProofExamples = do
    ex $ do
        s ["Let", m eqs_, "consist of the following equations"]
        let succ = fn "succ"
        itemize $ do
            let x = "X"
            item $ m $ x + 0 =: x
            let y = "Y"
            item $ m $ x + succ y =: succ (x + y)
        s ["Using", m $ res eqs_, "on", m $ succ (succ 0) + succ 0, "yields the following", equalityProof]
        ma $ succ (succ 0) + succ 0 =: succ (succ (succ 0) + 0) =: succ (succ (succ 0))

infiniteComputationsDefinition :: Note
infiniteComputationsDefinition = de $ do
    lab infiniteComputationsDefinitionLabel
    let a_ = "a"
        a = fn a_
    s ["An", equationalTheory, m et_, "is said to have", infiniteComputations', "if there is a", function, m $ fun a_ naturals ta_, "as follows"]
    let n = "n"
    ma $ a 0 `rr` a 1 `rr` a 2 `rr` dotsb `rr` a n `rr` a (n + 1) `rr` dotsb

terminatingDefinition :: Note
terminatingDefinition = de $ do
    lab terminatingDefinitionLabel
    s ["An", equationalTheory, m et_, "is said to be", terminating', "when it does not have", infiniteComputations]

terminatingExamples :: Note
terminatingExamples = do
    let a = "a"
        b = "b"
    ex $ s ["For", m $ eqs_ =: setof (a =: b) <> ",", m $ res eqs_, "is", terminating]
    ex $ s ["For", m $ eqs_ =: setofs [a =: b, b =: a] <> ",", m $ res eqs_, "is not", terminating]

reachingNotation :: Note
reachingNotation = de $ do
    let u = "u"
        v = "v"
    s ["Let", m et_, "be an", equationalTheory, and, m u, and, m v, terms, "in", m ta_]
    s ["We define the following abbreviation"]
    let t = ("t" !:)
        t1 = t 1
        t2 = t 2
        n = "n"
        tn = t n
    ma $ u ->* v === te (list t1 t2 tn) (u `rr` t1 `rr` t2 `rr` dotsb `rr` tn `rr` v)

confluenceDefinition :: Note
confluenceDefinition = de $ do
    lab confluenceDefinitionLabel
    lab confluentDefinitionLabel
    s ["An", equationalTheory, m et_, "is said to have the property of", confluence', "if the following holds"]
    let t = ("t" !:)
        t1 = t 1
        t2 = t 2
        t3 = t 3
        t4 = t 4
    ma $ fa (cs [t1, t2, t3] ∈ ta_) $ (pars $ t1 ->* t2 ∧ t1 ->* t3) ⇒ (pars $ te (t4 ∈ ta_) $ t2 ->* t4 ∧ t3 ->* t4)

confluenceExamples :: Note
confluenceExamples = do
    let a = "a"
        b = "b"
        c = "c"
    ex $ s ["For", m $ eqs_ =: setofs [a =: b, a =: c] <> ",", m $ res eqs_, "is not", confluent]
    ex $ s ["For", m $ eqs_ =: setofs [a =: b, a =: c, b =: c] <> ",", m $ res eqs_, "is", confluent]


