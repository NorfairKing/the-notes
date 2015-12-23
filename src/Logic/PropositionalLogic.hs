module Logic.PropositionalLogic where

import           Notes

import           Logic.AbstractLogic                  (complete, grammar,
                                                       inference, sound)
import           Logic.AbstractLogic.Macro

import           Logic.PropositionalLogic.Macro
import           Logic.PropositionalLogic.Terms
import           Logic.PropositionalLogic.TruthTables

propositionalLogicS :: Note
propositionalLogicS = note "propositional-logic" $ do
    section "Propositional Logic"
    propositionalLogicDefinition
    truthTables
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


truthTables :: Note
truthTables = do
    nte $ do
        s ["Truth tables are a very common and naive way of reasoning about sentences propositional logic"]
        s ["A cell in a truth table represents the value of the subexpression in the column for the a values of the symbols in that row"]
        s ["The validity of a proposition is checked by building the truth table for the sentence and checking whether all the values in the column for the sentence are true"]

        hereFigure $ do
            truthTableOf $ Not (Symbol "A")
        hereFigure $ do
            truthTableOf $ Or (Symbol "A") (Symbol "B")
            m quad
            truthTableOf $ And (Symbol "A") (Symbol "B")
        hereFigure $ do
            truthTableOf $ Implies (Symbol "A") (Symbol "B")
            m quad
            truthTableOf $ Equiv (Symbol "A") (Symbol "B")
            caption "Elementary truth tables"

    nte $ do
        s ["Eventhough truth tables are valid way to prove or disprove any propositional sentence, they are not practical in practice because they require an exponential amount of space with respect to the numbor of symbols in the sentence"]
        hereFigure $ do
            truthTableOf $ Implies (Implies (Symbol "P") (Symbol "Q")) (Implies (Not (Symbol "Q")) (Not (Symbol "P")))
            caption "Truth tables quickly become very large"


normalForms :: Note
normalForms = do
    subsection "Normal forms"
    conjunctiveNormalForm

conjunctiveNormalForm :: Note
conjunctiveNormalForm = do
    subsubsection "Conjunctive Normal Form"
    de $ do
      s ["A sentence in propositional logic is said to be in ", term "conjunctive normal form", or, term "clausal normal form", " (", term "CNF", ") if it is a conjunction of clauses where a clause is a disjunction of literals"]
    thm $ do
        s ["Every sentence propositional logic can be converted into an equivalent formula that is in CNF"]
        np
        s ["There is a famous transformation called the ", term "Tseitin transformation", " that does exactly this"]
        cite tseitinTransformation


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
inferences = do
    subsection "Inference in propositional logic"
    resolution

resolution :: Note
resolution = do
    de $ do
        s ["The ", inference, " ", term "rule of resolution", " is an inference in proposition logic"]
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

    thm $ do
        s ["This ", inference, " is ", sound, and, complete, "."]
        toprove

    nte $ do
        s ["Eventhough this ", inference, " is ", sound, and, complete, ", finding proofs can be difficult as search spaces become exponentially large"]
        citneeded

  where
    vsep = separated lorsign
    a = "a"
    b = "b"
    k = "k"
    l = "l"
    i = "i"
    j = "j"
