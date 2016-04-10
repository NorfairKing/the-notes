module ProgramAnalysis.Main where

import           Notes

import qualified Data.Text                      as T
import qualified Prelude                        as P

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
-- import Functions.Order.Macro
import           Functions.Order.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Relations.Orders.Hasse
import           Relations.Orders.Macro
import           Relations.Orders.Terms
import           Sets.Basics.Terms

-- import           ProgramAnalysis.Macro
-- import           ProgramAnalysis.Terms

programAnalysisC :: Note
programAnalysisC = chapter "Program analysis" $ do
    intervalAbstraction

intervalAbstraction :: Note
intervalAbstraction = section "Interval abstraction" $ do
    abstractDomainForIntervalAbstraction


abstractDomainForIntervalAbstraction :: Note
abstractDomainForIntervalAbstraction = do
    let zi = integers ^ infty
    s ["Define", m zi, "as", m $ integers ∪ setofs [minfty, pinfty]]
    let is = "I"
    let a = "a"
        b = "b"
    s ["Define ", m is, "as the", set, "of integer intervals"]
    let boti = bot !: is
    ma $ is =: ((setof boti) ∪ (setcmpr (ccint a b) (cs [a, b] ∈ zi)))
    s ["Now", m $ relposet is ("" ⊆ ""), "is a", lattice]
    toprove
    s ["Part of its Hasse Diagram is show below"]
    s ["Because the", lattice, "is of course", infinite, "most of its elements are omitted"]
    let n = 2 :: P.Int
        showt = T.pack . show
    s ["The following diagram only depicts the sublattice where finite bounds of intervals are smaller in absolute value than", m $ raw $ showt n]
    let bott = "bot"
        tuples = [(a, b) | a <- [-n..n], b <- [a..n]]
        showtup (a, b) = tup (showt a, showt b)
        tup (a, b) = "[" <> a <> ", " <> b <> "]"
        pinfty = "+i" :: Text
        minfty = "-i" :: Text
        topt = "[-i, +i]"
        pinftys = [ (i, pinfty) | i <- [-n..n]]
        pinftyts = P.map (\(i, j) -> tup ((showt i), j)) pinftys
        minftys = [ (minfty, i) | i <- [-n..n]]
        minftyts = P.map (\(i, j) -> tup (i, (showt j))) minftys
    hasseFig 7 $ hasseDiagram
            (bott : topt : minftyts P.++ pinftyts P.++ P.map showtup tuples)
            (
                [(bott, showtup i) | i <- tuples]
                P.++
                [(bott, i) | i <- minftyts]
                P.++
                [(bott, i) | i <- pinftyts]
                P.++
                [(tup (a, showt b), tup (x, showt y)) | (x,y) <- minftys, (a, b) <- minftys, b P.<= y]
                P.++
                [(showtup i, tup (x, showt y)) | (x,y) <- minftys, i@(_,b) <- tuples, b P.<= y]
                P.++
                [(showtup i1, showtup i2) | i1@(a, b) <- tuples, i2@(c, d) <- tuples, a P.>= c, b P.<= d]
                P.++
                [(showtup i, tup (showt x, y)) | (x,y) <- pinftys, i@(a,_) <- tuples, a P.>= x]
                P.++
                [(tup (showt a, b), tup (showt x, y)) | (x,y) <- pinftys, (a, b) <- pinftys, x P.<= a]
                P.++
                [(i, topt) | i <- minftyts]
                P.++
                [(i, topt) | i <- pinftyts]
                P.++
                [(showtup i, topt) | i <- tuples]
            )
    s ["Note the following about this", lattice]
    let a = "a"
        b = "b"
        c = "c"
        d = "d"
        i1 = ccint a b
        i2 = ccint c d
    ma $ i1 ⊆ i2 <> text " if " <> c <= a ∧ b <= d
    ma $ i1 ⊔ i2 =: ccint (minof $ setofs [a, c]) (maxof $ setofs [b, d])
    ma $ i1 ⊓ i2 =: (cases $ do
                ccint (minof (setofs [a, c])) (minof (setofs [b, d])) <> text " if " <> minof (setofs [a, c]) <= minof (setofs [b, d])
                lnbk
                bot <> text " otherwise"
            )

    let lab = "Lab"
        store = "Store"
        pss = powset store

    subsection "Concrete domain" $ do
        s ["In the concrete domain of interval analysis, at every program counter, we will keep the set of concrete states that may arise at that label"]

        s ["Let", m lab, "be a", set, "of program labels"]
        s ["These represent specific positions in the program and are usually almost equivalent to line numbers"]
        s ["Let", m store, "be a", set, "of possible states of a program"]
        s ["This", set, "encompasses all assignments of values to variables but not non-reproducable state like a system clock"]

        let ff = "F"
            sseqo = overset cdot_ subseteq_
        s ["We then have the following", completeLattice, m $ relposet ff sseqo]
        let f = "f"
        s [the, set, m ff, "is defined to be the set of", functions, m $ ff =: setcmpr f (fun f lab pss)]
        s [the, partialOrder, m sseqo, "is defined as follows"]
        let x = "x"
            f1 = f !: 1
            f2 = f !: 2
            (<<) = inposet (overset cdot_ subseteq_)
        ma $ fas [f1, f2] $ f1 << f2 === te x (fn f1 x ⊆ fn f2 x)
        let (∩.) = binop $ overset cdot_ setinsign
            (∪.) = binop $ overset cdot_ setunsign
            sfunc a b c = func a lab pss b c
        s ["Note that the", meet, and, join, "operations look as follows"]
        ma $ sfunc (f1 ∩. f2) x $ fn f1 x ∩ fn f2 x
        ma $ sfunc (f1 ∪. f2) x $ fn f1 x ∪ fn f2 x
        s ["The bottom and top functions look as follows"]
        let botf = overset cdot_ bot
            topf = overset cdot_ top
        ma $ sfunc botf unmatched emptyset
        ma $ sfunc topf unmatched store

    subsection "Collecting semantics" $ do
        let action = "Action"
        let a = "a"
        s ["Let", m action, "be a", set, "of possible statements (actions)"]
        let cintr a = sqbrac a !: "C"
        s ["For every", m action, m a, "we define a", defineTerm "concrete interpretation", m $ cintr a]
        let p = "P"
            program' = defineTerm "program"
            program = ix "program"
        s ["A", program', m p, "is a", subset, "of", m $ lab ⨯ action ⨯ lab, "with the following property"]
        let l = "l"
            li = l !: "in"
            lo = l !: "out"
            a  = "a"
            li1 = li !: 1
            li2 = li !: 2
            lo1 = lo !: 1
            lo2 = lo !: 2
            a1 = a !: 1
            a2 = a !: 2
        ma $ fas [triple li1 a1 lo1 ∈ p, triple li2 a2 lo2 ∈ p] $ (pars $ li1 =: li2 ∧ lo1 =: lo2) ⇒ (a1 =: a2)
        s ["Intuitively: every statement has an enter label and an exit label"]
        let fc = "F" !: "C"
        s ["We define a", function, m fc, "that represents how the semantics of a", program, "are collected during execution"]
        ma $ fun fc (pars $ lab → pss) (pars $ lab → pss)

        let f = "f"
            f' = "f" <> "'"
            l' = l <> "'"
        ma $ fn (fc !: p) f =: func f' lab pss l (cases $ do
                    store <> text " if " <> l <> text " is the initial label"
                    lnbk
                    setuncmp (triple l' a l ∈ p) $ fn (cintr a) (fn f l')
                )

        s [the, leastFixedPoint, "of", m fc, "are the", program <> "'s", defineTerm "collecting semantics"]

        s ["The purpose of abstract interpretation is to approximate this", function]


    subsection "Carthesian abstraction" $ mempty

