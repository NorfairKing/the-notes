module Logic.PropositionalLogic where

import           Notes

import           Prelude                              (map)

import           Functions.Basics
import           Functions.BinaryOperation

import           Logic.AbstractLogic.Macro
import           Logic.AbstractLogic.Terms

import           Logic.PropositionalLogic.Macro
import           Logic.PropositionalLogic.Resolution
import           Logic.PropositionalLogic.Sentence
import           Logic.PropositionalLogic.Terms
import           Logic.PropositionalLogic.TruthTables

propositionalLogicS :: Note
propositionalLogicS = note "propositional-logic" $ do
    section "Propositional Logic"
    propositionalLogicDefinition
    note "world" $ do
        worldDefinition
        worldExamples
    note "model" $ do
        modelDefinition
        modelsOfDefinition
        equivalentDefinitionEntailment
    note "valid" $ do
        validDefinition
        validExamples
    note "satisfiable" $ do
        satisfiableDefinition
        satisfiableExamples
    note "unsatisfiable" $ do
        unsatisfiableDefinition
        unsatisfiableExamples
        unsatisfiableMeansNegativeIsTrue
    note "equivalent" $ do
        logicallyEquivalentDefinition
        logicallyEquivalentExample

    truthTables
    equivalences

    normalForms
    inferences

propositionalLogicDefinition :: Note
propositionalLogicDefinition = do
    de $ do
        lab propositionalLogicDefinitionLabel
        s ["The ", propositionalLogic', " has a ", grammar, " ", m g, " and only two axioms"]
        enumerate $ do
            item $ do
                s [m g, " defines well formed formulas recursively with the following cases"]
                itemize $ do
                    item $ do
                        s [dquoted true, " and ", dquoted false, " are sentences"]
                    item $ do
                        s ["So-called propositional symbols, boolean variables, are sentences"]
                    item $ do
                        s ["If ", m ss, " is a sentence, then ", m $ neg ss, " is a sentence"]
                    item $ do
                        s ["If ", m s1, " and ", m s2, " are sentences, then ", m $ s1 ∨ s2, " is a sentence"]
                    item $ do
                        s ["If ", m s1, " and ", m s2, " are sentences, then ", m $ s1 ∧ s2, " is a sentence"]
            item $ do
                s ["The semantics of ", propositionalLogic, " sentences are defined recursively as follows"]
                itemize $ do
                    item $ do
                        s ["The sentences ", dquoted true, " and ", dquoted false, " are respectively asserted to be true and false"]
                    item $ do
                        s [m $ neg ss, " is true only if ", m ss, " is not"]
                    item $ do
                        s [m $ s1 ∨ s2, " is true if ", m s1, " is true, ", m s2, " is true or both are true"]
                    item $ do
                        s [m $ s1 ∧ s2, " is true if ", m s1, " is true and ", m s2, " is true"]
        s ["In propositional logic, a world defines a truth value to every propositional symbol"]

    nte $ do
        lab implicationDefinitionLabel
        lab equivalenceDefinitionLabel
        "There are some very common notational shorthands in propositional logic."
        itemize $ do
            item $ s [implication', ": ", dquoted (m $ s1 ⇒ s2), " for ", dquoted (m $ neg s1 ∨ s2)]
            item $ s [equivalence', ": ", dquoted (m $ s1 ⇔ s2), " for ", dquoted (m $ (pars $ s1 ⇒ s2) ∧ (pars $ s2 ⇒ s1))]

  where
    ss = "S"
    s1 = ss !: 1
    s2 = ss !: 2
    g = ("G" !: mathbb "I")

booleanValueDefinition :: Note
booleanValueDefinition = de $ do
    lab booleanValueDefinitionLabel
    s ["A ", booleanValue', " is an element of the set ", m $ setofs [true, false]]

worldDefinition :: Note
worldDefinition = de $ do
    lab worldDefinitionLabel
    s ["A logical ", world', " is a set of assignments of boolean values to propositional symbols"]
    s ["More rigorously, a ", world, " can be viewed as a ", function_, " from a set of symbols to ", m $ setofs [true, false]]

worldExamples :: Note
worldExamples = ex $ do
    s ["The following ", function, " is a world"]
    ma $ do
        let a = "A"
        let b = "B"
        setofs [tuple a true, tuple b false]

modelDefinition :: Note
modelDefinition = de $ do
    lab modelDefinitionLabel
    s ["We say a world ", m "m", " is a ", model', " of an expression ", m alpha, " if ", m alpha, " is true in ", m "m"]

modelsOfDefinition :: Note
modelsOfDefinition = do
    de $ s ["The set of all models of an expression ", m alpha, " is denoted as ", m (lmo alpha), "."]

    nte $ do
        s ["With a little notation overloading we also denote ", dquoted (s ["The intersection of the set of all models of the expressions in a set ", m "S"]), " as ", m (lmo "S")]
        ma $ lmo "S" `eq` setincmp ("s" ∈ "S") (lmo "s")


equivalentDefinitionEntailment :: Note
equivalentDefinitionEntailment = de $ do
    s ["Another way of expressing the fact that an expression ", m alpha, " is entailed by a ", knowledgeBase, " ", m lkb, ": ", m (lkb `lent` alpha), " is using models"]
    ma $ lmo lkb ⊆ lmo alpha

validDefinition :: Note
validDefinition = de $ do
    lab validDefinitionLabel
    s ["A ", sentence, " is called ", valid', " if it is ", true, " in all ", world, "s"]

validExamples :: Note
validExamples = ex $ do
    s ["The following sentence is valid"]
    ma $ do
        let a = "A"
        a ⇔ a

satisfiableDefinition :: Note
satisfiableDefinition = de $ do
    lab satisfiableDefinitionLabel
    s ["A ", sentence, " is called ", satisfiable', " if there exists a ", world, " in which it is ", true]

satisfiableExamples :: Note
satisfiableExamples = do
    ex $ do
        s ["The following sentence is ", satisfiable, " but not valid"]
        ma $ do
            let a = "A"
            a

unsatisfiableDefinition :: Note
unsatisfiableDefinition = de $ do
    lab unsatisfiableDefinitionLabel
    s ["A ", sentence, " is called ", unsatisfiable', " if it is not ", true, " in any world"]

unsatisfiableExamples :: Note
unsatisfiableExamples = do
    ex $ do
        s ["The following sentence is ", unsatisfiable]
        ma $ do
            let a = "A"
            a ∧ neg a

unsatisfiableMeansNegativeIsTrue :: Note
unsatisfiableMeansNegativeIsTrue = thm $ do
    s ["A ", knowledgeBase, " ", m lkb, " entails a sentence if and only if the negated sentence is ", unsatisfiable]
    ma $ do
        let a = "A"
        (lkb `lent` alpha) ⇔ (neg a <> text " is unsatisfiable")

logicallyEquivalentDefinition :: Note
logicallyEquivalentDefinition = de $ do
    lab logicallyEquivalentDefinitionLabel
    s ["Two ", sentence, "s are called ", logicallyEquivalent', " if in any world, either both are true or neither are true"]

logicallyEquivalentExample :: Note
logicallyEquivalentExample = ex $ do
    let (p, q) = ("P", "Q")
    s ["The sentences ", m $ p ⇒ q, " and ", m $ neg q ⇒ neg p, " are ", logicallyEquivalent]

truthTables :: Note
truthTables = note "truth-tables" $ do
    subsection "Truth tables"
    s ["Truth tables are a very common and naive way of reasoning about sentences propositional logic"]
    s ["A cell in a truth table represents the value of the subexpression in the column for the a values of the symbols in that row"]
    s ["The validity of a proposition can be checked by building the truth table for the sentence and checking whether all the values in the column for the sentence are true"]
    ex $ do
        let a = Literal $ Symbol "A"
            b = Literal $ Symbol "B"
        hereFigure $ do
            truthTableOf $ Not b
        hereFigure $ do
            truthTableOf $ Or a b
            m quad
            truthTableOf $ And a b
        hereFigure $ do
            truthTableOf $ Implies a b
            m quad
            truthTableOf $ Equiv a b
            caption "Elementary truth tables"

    nte $ do
        s ["Eventhough truth tables are valid way to prove or disprove any propositional sentence, they are not practical in practice because they require an exponential amount of space with respect to the numbor of symbols in the sentence"]
        hereFigure $ do
            let sym = Literal . Symbol
                [p, q, r, s] = map sym ["P", "Q", "R", "S"]
            truthTableOf $ Equiv (Implies p q) (Implies (Not r) (Not s))
            caption "Truth tables quickly become very large"

equivalences :: Note
equivalences =  note "equivalences" $ do
    andCommutativity
    andAssociativity
    orCommutativity
    orAssociativity
    doubleNegationElimination
    contraposition
    deMorgan1
    deMorgan2
    distributivityOrAnd
    distributivityAndOr

equivalenceProof :: Sentence -> Sentence -> Note
equivalenceProof s1 s2 = do
    ma $ renderSentence $ Equiv s1 s2
    proof $ do
        noindent
        hereFigure $ truthTableOfExprs [s1, s2]

andCommutativity :: Note
andCommutativity = thm $ do
    s [m ("" ∧ ""), " is ", commutative]
    let (a, b) = ("A", "B")
    equivalenceProof (And a b) (And b a)

andAssociativity :: Note
andAssociativity = thm $ do
    s [m ("" ∧ ""), " is ", associative]
    let (a, b, c) = ("A", "B", "C")
    equivalenceProof (And a (And b c)) (And (And a b) c)

orCommutativity :: Note
orCommutativity = thm $ do
    s [m ("" ∨ ""), " is ", commutative]
    let (a, b) = ("A", "B")
    equivalenceProof (Or a b) (Or b a)

orAssociativity :: Note
orAssociativity = thm $ do
    s [m ("" ∨ ""), " is ", associative]
    let (a, b, c) = ("A", "B", "C")
    equivalenceProof (Or a (Or b c)) (Or (Or a b) c)

doubleNegationElimination :: Note
doubleNegationElimination = thm $ do
    s ["Double negation"]
    let a = "A"
    equivalenceProof a $ Not $ Not a

contraposition :: Note
contraposition = thm $ do
    s [term "Contraposition"]
    let (a, b) = ("A", "B")
    equivalenceProof (Implies a b) (Implies (Not b) (Not a))

deMorgan1 :: Note
deMorgan1 = thm $ do
    s ["First law of ", term "De Morgan"]
    let (a, b) = ("A", "B")
    equivalenceProof (Not $ Or a b) (And (Not a) (Not b))

deMorgan2 :: Note
deMorgan2 = thm $ do
    s ["Second law of ", term "De Morgan"]
    let (a, b) = ("A", "B")
    equivalenceProof (Not $ And a b) (Or (Not a) (Not b))

distributivityOrAnd :: Note
distributivityOrAnd = thm $ do
    s [m $ "" ∨ "", " is ", distributive, " over ", m $ "" ∧ ""]
    let (a, b, c) = ("A", "B", "C")
    equivalenceProof (Or a (And b c)) (And (Or a b) (Or a c))

distributivityAndOr :: Note
distributivityAndOr = thm $ do
    s [m $ "" ∧ "", " is ", distributive, " over ", m $ "" ∨ ""]
    let (a, b, c) = ("A", "B", "C")
    equivalenceProof (And a (Or b c)) (Or (And a b) (And a c))

normalForms :: Note
normalForms = do
    subsection "Normal forms"
    conjunctiveNormalFormS

conjunctiveNormalFormS :: Note
conjunctiveNormalFormS = note "cnf" $ do
    subsubsection "Conjunctive Normal Form"
    de $ do
        lab conjunctiveNormalFormDefinitionLabel
        s ["A sentence in propositional logic is said to be in ", conjunctiveNormalForm', or, term "clausal normal form", " (", term "CNF", ") if it is a conjunction of clauses where a clause is a disjunction of literals"]
    thm $ do
        s ["Every sentence propositional logic can be converted into an equivalent formula that is in CNF"]
        s ["There is a famous transformation called the ", term "Tseitin transformation", cite tseitinTransformation, " that does exactly this"]

        s ["The Tseitin transformation works by applying the following steps"]
        enumerate $ do
            item $ do
                s ["Remove biconditionals: Inversely apply the notational shorthand for ", m ("" ⇔ "")]
            item $ do
                s ["Remove conditionals: Inversely apply the notational shorthand for ", m ("" ⇒ "")]
            item $ do
                s ["Move all negations inwards by applying the De Morgan laws and removing double negations"]
            item $ do
                s ["Use the distributive laws to obtain a formula in CNF"]
        np
    ex $ do
        let (p, q) = ("P", "Q")
            sen = Equiv (Implies p q) (Implies (Not q) (Not p))
        renderTransformation sen
        s ["The Tseitin transformation, applied to ", m $ renderSentence sen]
    de $ do
        let n = "n"
        s ["A sentence is said to be in ", m n, "-CNF if it is in ", conjunctiveNormalForm, " where each disjunction contains exactly ", m n, " literals"]
    thm $ do
        let n = "n"
        s ["Given ", m n, " distinct propositional symbols, there exist ", m $ 2 * n ^ 2 + 1, " semantically distinct ", m 2, "-CNF sentences"]

        proof $ do
            s ["Each of the ", m n, " symbols can occur as-is or negated"]
            s ["This gives us ", m $ 2 * n, " symbols to choose from"]
            s ["In each clause, exactly ", m 2, " literals can be chosen"]
            s ["There are ", m $ (2 * n) `choose` 2, " ways to do so if we consider distinct literals in each clause"]
            let a = "A"
            s ["Count ", m $ 2 * n, " more literals for clauses of the form ", m $ a ∨ a]
            s ["Clauses of the form ", m $ a ∨ neg a, " all evaluate to true and should therefore not be counted"]
            s ["In total this leaves ", m $ pars (2 * n ^ 2 - n) + (2 * n) - pars (n - 1), " possible semantically distinct ", m 2, "-CNF expressions"]


tseitinTransformation :: Reference
tseitinTransformation = Reference article "tseitin68" $
    [
      ("author", "Tseitin, G. S.")
    , ("journal", "Studies in Mathematics and Mathematical Logic")
    , ("pages", "234-259")
    , ("title", "On the complexity of derivations in the propositional calculus")
    , ("volume", "Part II")
    , ("year", "1968")
    ]

inferences :: Note
inferences = note "inference" $ do
    subsection "Inference in propositional logic"
    modusPonensInProp
    resolution

modusPonensInProp :: Note
modusPonensInProp = note "modus-ponens" $ thm $ do
    s ["The ", modusPonens_, " ", inference, " rule in ", propositionalLogic, " is ", sound, " but not ", complete]

    toprove


resolution :: Note
resolution = note "resolution" $ do
    resolutionDefinition
    resolutionSoundAndComplete
    resolutionProofs

resolutionDefinition :: Note
resolutionDefinition = de $ do
    s ["The ", inference, " ", term "rule of resolution", " is an ", inference, " in proposition logic"]
    s ["It assumes that sentences are in ", conjunctiveNormalForm]
    s ["Let ", m a, and, m b, " be propositional formulae in CNF."]
    ma $ do
        a =: vsep [a !: 1, a !: 2, dotsc, a !: k]
        quad
        b =: vsep [b !: 1, b !: 2, dotsc, b !: l]
    s ["Suppose also that, for some ", m i, and, m j, ", ", m (a !: i =: not (b !: j)), " holds"]
    ma $ do
        linf [vsep [a !: 1, a !: 2, dotsc, a !: k], vsep [b !: 1, b !: 2, dotsc, b !: l]] $
            vsep $
              [a !: 1, a !: 2, dotsc, a !: (i - 1), a !: (i + 1), dotsc, a !: k]
              ++
              [b !: 1, b !: 2, dotsc, b !: (j - 1), b !: (j + 1), dotsc, b !: k]
  where
    vsep = separated lorsign
    a = "a"
    b = "b"
    k = "k"
    l = "l"
    i = "i"
    j = "j"

resolutionSoundAndComplete :: Note
resolutionSoundAndComplete = do
    thm $ do
        s ["This ", inference, " is ", sound, and, complete, "."]
        toprove

    nte $ do
        s ["Eventhough this ", inference, " is ", sound, and, complete, ", finding proofs can be difficult as search spaces become exponentially large"]
        citneeded

resolutionProofs :: Note
resolutionProofs = do
    thm $ do
        let a = "A"
        s ["Given a ", knowledgeBase, " ", m lkb, and, " a ", sentence, " ", m alpha, " we can prove or disprove ", m alpha, " by showing that ", m $ not alpha ∧ andcomp (a ∈ lkb) a, " is ", unsatisfiable]
        toprove
    ex $ do
        let (a, b) = ("A", "B")
        let [as, bs] = map (Literal . Symbol) [a, b]
        let s1 = And (Or as bs) (Not as)
        let s2 = bs
        s ["We can prove ", m $ renderSentence s2, " from ", m $ renderSentence s1 , " as follows"]
        proofUnsatisfiable 3 s1 s2
    ex $ do
        let (a, b, c) = ("A", "B", "C")
        let [as, bs, cs] = map (Literal . Symbol) [a, b, c]
        let s11 = Equiv as (Or bs cs)
        let s12 = Not as
        let s1 = And s11 s12
        let s2 = Not bs
        s ["Suppose we have a ", knowledgeBase, " ", m $ setofs [renderSentence s11, renderSentence s12], " and let ", m $ alpha =: renderSentence s2]
        newline
        s ["First we convert all sentences to CNF"]
        renderTransformation s11
        s ["Now we add ", m $ neg alpha, " in conjunction with the sentences in the knowledge base and prove that the resulting sentence is unsatisfiable"]
        proofUnsatisfiable 10 s1 s2

    ex $ do
        let [a, b, c, d, g] = map (Literal . Symbol) ["A", "B", "C", "D", "G"]
        let s1 = And (And (And (And (Or a b) (Or (Not a) c)) (Or (Not b) d)) (Or (Not c) g)) (Or (Not d) g)
        let s2 = g
        proofUnsatisfiable 10 s1 s2



