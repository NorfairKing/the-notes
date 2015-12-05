module Functions.Order where

import           Notes

import           Relations.Orders (completeLattice, joinSemilattice_, lattice_,
                                   meetSemilattice_, poset_)
import           Sets.Basics      (set)

import           Functions.Basics (function)

makeDefs [
      "monotonic"
    , "Scott continuous"
    , "fixed point"
    , "fixed point region"
    , "ascending region"
    , "descending region"
    , "least fixed point"
    , "greatest fixed point"
    ]

order :: Notes
order = notesPart "orders" body

body :: Note
body = do
    section "Functions and orders"

    monotonicDefinition
    scottContinuousDefinition
    fixedPointDefinition
    leastFixedPointDefinition
    greatestFixedPointDefinition
    regions


regions :: Note
regions = do
    subsection "Regions"

    todo "weaken necessary properties of lattices in this section. For example, the ascending region can be defined for arbitrary posets. It is only for the partitioning theorem that a complete lattice is required."
    fixedPointRegionDefinition
    ascendingRegionDefinition
    descendingRegionDefinition

    fixedPointRegionIsIntersectionOfAscAndDesc
    regionPartitionTheorem
    topInDescendingRegion
    botInAscendingRegion
    ascendingRegionIsClosedUnderApplication
    descendingRegionIsClosedUnderApplication


monotonicDefinition :: Note
monotonicDefinition = de $ do
    lab monotonicDefinitionLabel
    s ["Let ", m $ relposet_ x rx, and, m $ relposet_ y ry, " each be a ", poset_, and, m $ fun f x y, " a function"]
    s [m $ fun f x y, " is said to be ", monotonic', " if it has the following property"]
    ma $ fa (cs [x1, x2] ∈ x) $ inposet_ rx x1 x2 ⇒ inposet_ ry (f_ x1) (f_ x2)
  where
    x1 = x !: 1
    x2 = x !: 2
    f = funrel_
    f_ = fn f
    x = "X"
    rx = partord !: x
    y = "Y"
    ry = partord !: y


scottContinuousDefinition :: Note
scottContinuousDefinition = de $ do
    lab scottContinuousDefinitionLabel
    s ["Let ", m $ rellat_ x rx, and, m $ rellat_ y ry, " each be a ", lattice_, and, m $ fun f x y, " a function"]
    s [m $ fun funrel_ x y, " is called ", scottContinuous', " if it has the following property"]
    ma $ fa (ss ⊆ x) $ f_ (sup ss) =: sup (f □ ss)
  where
    ss = "S"
    f = funrel_
    f_ = fn f
    x = "X"
    rx = partord !: x
    y = "Y"
    ry = partord !: y

fixedPointDefinition :: Note
fixedPointDefinition = de $ do
    lab fixedPointDefinitionLabel
    s ["Let ", m x, and, m y, " be ", set, "s ", m $ fun f x y, " be a function"]
    s ["An element ", m a, " of ", m x, " is called a ", fixedPoint', " of ", m f, " if ", m f, " leaves a unchanged"]
    ma $ fn f a =: a
  where
    f = funrel_
    a = "a"
    x = "X"
    y = "Y"

leastFixedPointDefinition :: Note
leastFixedPointDefinition = de $ do
    lab leastFixedPointDefinitionLabel
    s ["Let ", m rellat, " be a ", meetSemilattice_, and, m $ fun f x x, " a ", function]
    s ["The ", leastFixedPoint', " is defined as follows"]
    ma $ lfp f === inf (fix f)
  where
    f = funrel_
    x = latticeset


greatestFixedPointDefinition :: Note
greatestFixedPointDefinition = de $ do
    lab greatestFixedPointDefinitionLabel
    s ["Let ", m rellat, " be a ", joinSemilattice_, and, m $ fun f x x, " a ", function]
    s ["The ", greatestFixedPoint', " is defined as follows"]
    ma $ gfp f === sup (fix f)
  where
    f = funrel_
    x = latticeset

regionDec :: Note
regionDec = s ["Let ", m rellat, " be a ", completeLattice, and, m $ fun f x x, " a ", monotonic, " ", function]
  where
    f = funrel_
    x = latticeset

fixedPointRegionDefinition :: Note
fixedPointRegionDefinition = de $ do
    lab fixedPointRegionDefinitionLabel
    regionDec
    s ["The ", fixedPointRegion', " ", m $ fix f, " is the ", set, " of ", fixedPoint, "s of ", m latticeset]
    ma $ fix f === setcmpr (x ∈ latticeset) (x =: f_ x)
  where
    f = funrel_
    f_ = fn f
    x = "x"

ascendingRegionDefinition :: Note
ascendingRegionDefinition = de $ do
    lab ascendingRegionDefinitionLabel
    regionDec
    s ["The ", ascendingRegion', " ", m $ asc f, " is the following ", set]
    ma $ asc f === setcmpr (x ∈ latticeset) (x ⊆: f_ x)
  where
    f = funrel_
    f_ = fn f
    x = "x"

descendingRegionDefinition :: Note
descendingRegionDefinition = de $ do
    lab descendingRegionDefinitionLabel
    regionDec
    s ["The ", descendingRegion', " ", m $ desc f, " is the following ", set]
    ma $ desc f === setcmpr (x ∈ latticeset) (f_ x ⊆: x)
  where
    f = funrel_
    f_ = fn f
    x = "x"


fixedPointRegionIsIntersectionOfAscAndDescLabel :: Label
fixedPointRegionIsIntersectionOfAscAndDescLabel = Label Theorem "fixed-point-region-is-intersection-of-ascending-region-and-descending-region"

fixedPointRegionIsIntersectionOfAscAndDesc :: Note
fixedPointRegionIsIntersectionOfAscAndDesc = thm $ do
    lab fixedPointRegionIsIntersectionOfAscAndDescLabel
    regionDec
    ma $ fix f =: asc f ∩ desc f
    toprove
  where
    f = funrel_

regionPartitionTheoremLabel :: Label
regionPartitionTheoremLabel = Label Theorem "region-partition-theorem"

regionPartitionTheorem :: Note
regionPartitionTheorem = thm $ do
    lab regionPartitionTheoremLabel
    regionDec
    s [m $ setofs [asc f \\ fix f, fix f, desc f \\ fix f], " is a partition of ", m x]
    toprove
  where
    f = funrel_
    x = latticeset

topInDescendingRegionLabel :: Label
topInDescendingRegionLabel = Label Theorem "top-element-is-in-descending-region"

topInDescendingRegion :: Note
topInDescendingRegion = thm $ do
    lab topInDescendingRegionLabel
    regionDec
    ma $ bot ∈ asc f
  where
    f = funrel_

botInAscendingRegionLabel :: Label
botInAscendingRegionLabel = Label Theorem "bot-element-is-in-ascending-region"

botInAscendingRegion :: Note
botInAscendingRegion = thm $ do
    lab botInAscendingRegionLabel
    regionDec
    ma $ top ∈ desc f
  where
    f = funrel_

ascendingRegionIsClosedUnderApplicationLabel :: Label
ascendingRegionIsClosedUnderApplicationLabel = Label Theorem "ascending-region-is-closed-under-application"

ascendingRegionIsClosedUnderApplication :: Note
ascendingRegionIsClosedUnderApplication = thm $ do
    lab ascendingRegionIsClosedUnderApplicationLabel
    regionDec
    ma $ fa (a ∈ x) $ x ∈ asc f ⇒ f_ x ∈ asc f
  where
    f = funrel_
    f_ = fn f
    a = "x"
    x = latticeset

descendingRegionIsClosedUnderApplicationLabel :: Label
descendingRegionIsClosedUnderApplicationLabel = Label Theorem "descending-region-is-closed-under-application"

descendingRegionIsClosedUnderApplication :: Note
descendingRegionIsClosedUnderApplication = thm $ do
    lab descendingRegionIsClosedUnderApplicationLabel
    regionDec
    ma $ fa (a ∈ x) $ x ∈ desc f ⇒ f_ x ∈ desc f
  where
    f = funrel_
    f_ = fn f
    a = "x"
    x = latticeset















