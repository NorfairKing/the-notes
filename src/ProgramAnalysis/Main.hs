module ProgramAnalysis.Main where

import           Notes

import qualified Data.Text              as T
import qualified Prelude                as P

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

    s ["Now", m $ relposet is ("" <= ""), "is a", lattice]
    toprove
    s ["Part of its Hasse Diagram is show below"]
    s ["Because the", lattice, "is of course", infinite, "most of its elements are omitted"]
    let bott = "bot"
        topt = "[...]"
        n = 2 :: P.Int
        tuples = [(a, b) | a <- [-n..n], b <- [a..n]]
        showt = T.pack . show
        showtup (a, b) = "[" <> showt a <> ", " <> showt b <> "]"
    hasseFig 5 $ hasseDiagram
            (bott : topt : P.map showtup tuples)
            (
            [(bott, showtup i) | i <- tuples]
            P.++
            [(showtup i1, showtup i2) | i1@(a, b) <- tuples, i2@(c, d) <- tuples, a P.>= c, b P.<= d]
            P.++
            [(showtup i, topt) | i <- tuples]
            )
