module Functions.Order where

import           Notes

import           Relations.Orders (completeLattice_, joinSemilattice_, lattice_,
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

    fixedPointRegionDefinition
    ascendingRegionDefinition
    descendingRegionDefinition


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

regionDec :: Note
regionDec = s ["Let ", m rellat, " be a ", completeLattice_, and, m $ fun f x x, " a ", monotonic, " ", function]
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
