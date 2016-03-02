module Functions.SetFunctions where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Sets.Basics.Terms

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms

import           Functions.SetFunctions.Terms

setFunctionsS :: Note
setFunctionsS = section "Set functions" $ do
    setFunctionDefinition

    submodularitySS

submodularitySS :: Note
submodularitySS = subsection "Submodularity" $ do
    subModularFunctionDefinition
    submodularityIsClosedUnderNonnegativeLinearCombinationTheorem
    submodularityIsClosedUnderRandomProcessesTheorem
    todo "multi-objective optimisation property!!"

setFunctionDefinition :: Note
setFunctionDefinition = de $ do
    lab setFunctionDefinitionLabel
    let x = "X"
        y = "Y"
    s ["Let", m x, "be a", set, "of", sets, and, "let", m y, "be a", set]
    s ["A", function, m fun_, "as follows is called a", setFunction']
    ma $ fun fun_ x y


subModularFunctionDefinition :: Note
subModularFunctionDefinition = de $ do
    lab submodularDefinitionLabel
    let o = comm0 "Omega"
    s ["Let", m o, "be a set"]
    let f' = fun_
        f = fn f'
    s ["A", function, m $ fun f' (powset o) reals, "is called", submodular', "if it has the following property"]
    let x = "X"
        y = "Y"
        z = "z"
        x' = x ∪ setof z
        y' = y ∪ setof z
    ma $ fa (x ⊆ o) $ fa (y ⊆ o) $ (x ⊆ y) ⇒ (fa (z ∈ (o \\ y)) $ f x' - f x >= f y' - f y)

submodularityIsClosedUnderNonnegativeLinearCombinationTheorem :: Note
submodularityIsClosedUnderNonnegativeLinearCombinationTheorem = thm $ do
    lab submodularityIsClosedUnderNonnegativeLinearCombinationTheoremLabel
    s ["A nonnegative linear combination of", submodular, functions, "is", submodular]
    toprove

submodularityIsClosedUnderRandomProcessesTheorem :: Note
submodularityIsClosedUnderRandomProcessesTheorem = thm $ do
    lab submodularityIsClosedUnderRandomProcessesTheoremLabel
    let o = comm0 "Omega"
    s ["Let", m o, "be a set"]
    let t = theta
        tt = comm0 "Theta"
        f' = "F" !: t
        f = fn f'
    s ["Let", m f', "be a function indexed by a parameter", m $ t ∈ tt]
    ma $ fun f' (powset o) reals
    s ["Let", m prm_, "be a", probabilityMeasure, "with universe", m tt]
    let g' = "g"
        g = fn g'
    s [the, function, m g', "as follows is", submodular, "if", m f', "is", submodular, "for every", m t]
    let a = "A"
    ma $ func g' (powset o) reals a $ g a =: sumcmp t (prob t * f a)
    toprove

