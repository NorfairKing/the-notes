module Cryptography.ComputationalProblems.Reductions where

import           Notes                                               hiding
                                                                      (cyclic,
                                                                      inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Composition.Macro
import           Functions.Order.Terms
import           Logic.FirstOrderLogic.Macro
import           Relations.Orders.Macro
import           Relations.Orders.Terms                              hiding
                                                                      (order)
import           Sets.Basics.Terms

import           Cryptography.SystemAlgebra.AbstractSystems.Terms

import           Cryptography.ComputationalProblems.Abstract.Macro
import           Cryptography.ComputationalProblems.Abstract.Terms

-- import           Cryptography.ComputationalProblems.Reductions.Macro
import           Cryptography.ComputationalProblems.Reductions.Terms



reductionsSS :: Note
reductionsSS = subsection "Reductions" $ do
    reductionDefinition
    reductionReeinterpretation
    compositionOfReductions
    todo "generalised reductions for lists of problems"


reductionDefinition :: Note
reductionDefinition = do
    let p = "p"
        q = "q"
    de $ do
        lab reductionDefinitionLabel
        lab reductionFunctionDefinitionLabel
        lab performanceTranslationFunctionDefinitionLabel
        s ["A", reduction', from, m q, to, m p]
        newline
        s ["Let", m p, and, m q, "be two", problems, and , m $ solvs p, and, m $ solvs q, sets, "of", solvers]
        let po = partord_
        s ["Let", m $ perfs p, and, m $ perfs q, "be the", sets, "of", performanceValues, "associated with", m p, and, m q, "respectively"]
        let pop = po !: p
            poq = po !: q
        s ["Let", m $ perfs p, and, m $ perfs q, "be equipped with the", partialOrders, m pop, and, m poq, "respectively"]
        newline
        let t_ = tau
            t = fn t_
            r_ = rho
            r = fn r_
            sl = "s"
        s ["A", tReduction' t_, "of", m q, to, m p, "is a", function, m r_, "that maps a", solver, for, m p, "onto a", solver, for, m q, ".."]
        ma $ func r_ (solvs p) (solvs q) sl (r sl)
        s ["... such that", m t_, "is a", monotonic', function, "as follows"]
        footnote $ s ["Monotonicity entails that a better", solver, "for", m p, "does not result in a worse", solver, "for", m q]
        let a = "a"
        ma $ func t_ (perfs p) (perfs q) a (t a)
        s [m r_, "is called the", reductionFunction', and, m t_, "is called the", performanceTranslationFunction']
        newline
        s ["The following equation then characterizes this", reduction]
        let (<<) = inposet poq
        ma $ fa (sl ∈ solvs p) $ t (perf p sl) << perf q (r sl)
    nte $ do
        s ["We use a", reduction, "of", m q, to, m p, "to build a", solver, for, m q, "when we have a", solver, for, m p]
    nte $ do
        s ["The characteristic inequality of a reduction of", m q, to, m p, "can be interpreted as implying a lower bound on the performance of any solver for", m q, "in terms of", m p, "or as implying an upper bound on the performance for any solver for", m p, "in terms of", m q]
    nte $ do
        s ["That", m tau, "needs to be", monotonic, "entails that a better", solver, for, m p, "won't make for a worse", solver, for, m q]
    de $ do
        lab reducibleDefinitionLabel
        s ["A", problem, m p, "is said to be", reducible, "to another", problem, m q, "if there exists a", reduction, "of", m p, to, m q]

reductionReeinterpretation :: Note
reductionReeinterpretation = thm $ do
    let p = "p"
        q = "q"
    let t_ = tau
        t = fn t_
        r_ = rho
        r = fn r_
        sl = "s"
    s ["A", tReduction t_, m r_, "of a", problem, m p, "to a", problem, m q, "can equivalently be interpreted as follows"]
    newline
    let l_ = lambda
        l = fn l_
    s ["Let", m $ fun l_ (perfs q) (perfs p), "be a", monotone, function, "satisfying the following inequality"]
    let (⊆:) = inposet $ partord_ !: p
    let a = "a"
    ma $ fa (a ∈ perfs p) $ a ⊆: l (t (a))
    s [the, reduction, "inequality can then be rephrased as follows"]
    ma $ fa (sl ∈ solvs p) $ perf p sl ⊆: l (perf q (r sl))

    proof $ do

        let (<<) = inposet $ partord_ !: q
        ma $ centeredBelowEachOther
            [ fa (sl ∈ solvs p) $ t (perf p sl) << perf q (r sl)
            , fa (sl ∈ solvs p) $ l (t (perf p sl)) ⊆: l (perf q (r sl))
            , fa (sl ∈ solvs p) $ perf p sl ⊆: l (perf q (r sl))
            ]



compositionOfReductions :: Note
compositionOfReductions = thm $ do
    lab compositionOfReductionsTheoremLabel
    textbf $ s [the, composition, "of", reductions]
    newline
    let p = "p"
        q = "q"
        r = "r"
    s ["Let", csa [m p, m q, m r], "be three", problems, and, csa [m $ solvs p, m $ solvs q, m $ solvs r], sets, "of", solvers]
    let po = partord_
    s ["Let", csa [m $ perfs p, m $ perfs q, m $ perfs r], "be the", sets, "of", performanceValues, "associated with", csa [m p, m q, m r], "respectively"]
    let pop = po !: p
        poq = po !: q
        por = po !: r
    s ["Let", csa [m $ perfs p, m $ perfs q, m $ perfs r], "be equipped with the", partialOrders, csa [m pop, m poq, m por], "respectively"]
    newline
    let t1_ = tau !: 1
        t1 = fn t1_
        t2_ = tau !: 2
        t2 = fn t2_
        r1_ = rho !: 1
        r1 = fn r1_
        r2_ = rho !: 2
        r2 = fn r2_
        sl = "s"
    s ["Let", m r1_, "be a", tReduction t1_, "of", m q, to, m p, "and let", m r2_, "be a", tReduction t2_, "of", m r, to, m q]
    s ["Then", m $ r2_ ● r1_, "is a", tReduction $ pars $ t2_ ● t1_, "of", m r, to, m p]

    proof $ do
        s ["That", m r1_, "is a", tReduction t1_, "of", m q, to, m p, "means the following"]
        let (<<) = inposet poq
        ma $ fa (sl ∈ solvs p) $ t1 (perf p sl) << perf q (r1 sl)
        let (<.) = inposet por
        s ["Composing both sides with the", monotonic, function, m t2_, "gives us the following"]
        ma $ fa (sl ∈ solvs p) $ t2 (t1 (perf p sl)) <. t2 (perf q (r1 sl))

        s ["That", m r2_, "is a", tReduction t2_, "of", m r, to, m q, "means the following"]
        ma $ fa (sl ∈ solvs q) $ t2 (perf q sl) <. perf r (r2 sl)

        s ["Precomposing both sides with ", m r1_, "gives us the following"]
        ma $ fa (sl ∈ solvs p) $ t2 (perf q (r1 sl)) <. perf r (r2 (r1 sl))

        s ["Combining these two inequalities yields the theorem"]
        ma $ fa (sl ∈ solvs p) $ t2 (t1 (perf p sl)) <. t2 (perf q (r1 sl)) <. perf r (r2 (r1 sl))
    todo "Proof with inequality from the reinterpretation"

