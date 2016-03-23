module FormalMethods.Main where

import           Notes                       hiding (constant, cyclic, inverse)

import           Functions.Application.Macro
import           Functions.Basics.Terms
import           Logic.FirstOrderLogic.Macro
import           Sets.Basics.Terms

import           FormalMethods.Macro
import           FormalMethods.Terms

formalMethods :: Note
formalMethods = chapter "Formal Methods" $ do
    signatureDefinition
    constantDefinition
    peanoExampleSig
    termAlgebraDefinition
    peanoExampleAlgebra
    equationDefinition
    equationalTheoryDefinition
    orientedEquationDefinition
    equationalDerivationDefinition
    peanoEquationalDerivationsExample

signatureDefinition :: Note
signatureDefinition = de $ do
    lab signatureDefinitionLabel
    lab arityDefinitionLabel
    s ["A", signature', m sig_, "is a", set, "of", function, "symbols, each with an", arity']

constantDefinition :: Note
constantDefinition = de $ do
    lab constantDefinitionLabel
    s ["A", constant', "is an element of a", signature, "with arity", m 0]

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

equationalTheoryDefinition :: Note
equationalTheoryDefinition = de $ do
    s ["Let", m sig_, "be a", signature, "and", m eqs_, "a set of", equations']
    s [m et_, "is called an", equationalTheory']

orientedEquationDefinition :: Note
orientedEquationDefinition = de $ do
    let t = "t"
        t' = "t'"
    s ["An", equation, m $ t =: t', "can be oriented"]
    s ["If it is oriented left, it is written as", m $ t <> leftarrow <> t']
    s ["If it is oriented right, it is written as", m $ t <> rightarrow <> t']

equationalDerivationDefinition :: Note
equationalDerivationDefinition = de $ do
    lab equationalDerivationDefinitionLabel
    s ["Let", m et_, "be an", equationalTheory]
    s ["An", equationalDerivation', "in", m et_, "is a list of", terms, "such that every pair of two successive", terms, "is an", equation, "in", m eqs_]

peanoEquationalDerivationsExample :: Note
peanoEquationalDerivationsExample = ex $ do
    s [the, equations, m eqs_, "defining the Peano natural numbers are the following"]
    let succ = fn "succ"
    itemize $ do
        let x = "X"
        item $ m $ x + 0 =: x
        let y = "Y"
        item $ m $ x + succ y =: succ (x + y)
    s ["Using", m $ res eqs_, "on", m $ succ (succ 0) + succ 0, "yields the following", equationalDerivation]
    ma $ succ (succ 0) + succ 0 =: succ (succ (succ 0) + 0) =: succ (succ (succ 0))


