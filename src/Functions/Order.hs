module Functions.Order where

import           Notes

import           Relations.Orders (lattice_, poset_)

makeDefs [
      "monotonic"
    , "Scott continuous"
    ]

order :: Notes
order = notesPart "orders" body

body :: Note
body = do
    section "Functions and orders"

    monotonicDefinition
    scottContinuousDefinition

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
