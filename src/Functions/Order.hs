module Functions.Order where

import           Notes

import           Relations.Basics       (reflexive_)
import           Relations.Orders       (antisymmetric_, boundedLattice_,
                                         completeLattice_, lattice_,
                                         partialOrderDefinitionLabel, poset_)
import           Relations.Preorders    (preorderDefinitionLabel)
import           Sets.Basics            (set)

import           Relations.Orders.Macro

import           Functions.Basics       (function)

import           Functions.Order.Macro

makeDefs [
      "monotonic"
    , "Scott continuous"
    , "fixed point"
    , "fixed point region"
    , "ascending region"
    , "descending region"
    , "least fixed point"
    , "greatest fixed point"
    , "Kleene chain"
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

    kleeneChainDefinition
    kleenesFixedPointTheorem


regions :: Note
regions = do
    subsection "Regions"

    fixedPointRegionDefinition
    ascendingRegionDefinition
    descendingRegionDefinition

    ascendingRegionIsClosedUnderApplication
    descendingRegionIsClosedUnderApplication

    topInDescendingRegion
    botInAscendingRegion

    fixedPointRegionIsIntersectionOfAscAndDesc


monotonicDefinition :: Note
monotonicDefinition = de $ do
    lab monotonicDefinitionLabel
    s ["Let ", m $ relposet x rx, and, m $ relposet y ry, " each be a ", poset_, and, m $ fun f x y, " a function"]
    s [m $ fun f x y, " is said to be ", monotonic', " if it has the following property"]
    ma $ fa (cs [x1, x2] ∈ x) $ inposet rx x1 x2 ⇒ inposet ry (f_ x1) (f_ x2)
  where
    x1 = x !: 1
    x2 = x !: 2
    f = funrel_
    f_ = fn f
    x = "X"
    rx = partord_ !: x
    y = "Y"
    ry = partord_ !: y


scottContinuousDefinition :: Note
scottContinuousDefinition = de $ do
    lab scottContinuousDefinitionLabel
    s ["Let ", m $ lat x rx, and, m $ lat y ry, " each be a ", lattice_, and, m $ fun f x y, " a function"]
    s [m $ fun funrel_ x y, " is called ", scottContinuous', " if it has the following property"]
    ma $ fa (ss ⊆ x) $ f_ (sup ss) =: sup (f □ ss)
  where
    ss = "S"
    f = funrel_
    f_ = fn f
    x = "X"
    rx = partord_ !: x
    y = "Y"
    ry = partord_ !: y

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
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", function]
    s ["The ", leastFixedPoint', " ", m $ lfp f, " of ", m f, " is defined as follows"]
    ma $ lfp f === inf (fix f)
  where
    f = funrel_
    x = posetset_


greatestFixedPointDefinition :: Note
greatestFixedPointDefinition = de $ do
    lab greatestFixedPointDefinitionLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", function]
    s ["The ", greatestFixedPoint', " ", m $ gfp f, " of ", m f, " is defined as follows"]
    ma $ gfp f === sup (fix f)
  where
    f = funrel_
    x = posetset_

fixedPointRegionDefinition :: Note
fixedPointRegionDefinition = de $ do
    lab fixedPointRegionDefinitionLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", function]
    s ["The ", fixedPointRegion', " ", m $ fix f, " is the ", set, " of ", fixedPoint, "s of ", m latset_]
    ma $ fix f === setcmpr (a ∈ latset_) (a =: f_ a)
  where
    f = funrel_
    f_ = fn f
    a = "x"
    x = posetset_

ascendingRegionDefinition :: Note
ascendingRegionDefinition = de $ do
    lab ascendingRegionDefinitionLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", function]
    s ["The ", ascendingRegion', " ", m $ asc f, " is the following ", set]
    ma $ asc f === setcmpr (a ∈ latset_) (a ⊆: f_ a)
  where
    f = funrel_
    f_ = fn f
    a = "x"
    x = posetset_

descendingRegionDefinition :: Note
descendingRegionDefinition = de $ do
    lab descendingRegionDefinitionLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", function]
    s ["The ", descendingRegion', " ", m $ desc f, " is the following ", set]
    ma $ desc f === setcmpr (a ∈ latset_) (f_ a ⊆: a)
  where
    f = funrel_
    f_ = fn f
    a = "x"
    x = posetset_

ascendingRegionIsClosedUnderApplicationLabel :: Label
ascendingRegionIsClosedUnderApplicationLabel = Label Theorem "ascending-region-is-closed-under-application"

ascendingRegionIsClosedUnderApplication :: Note
ascendingRegionIsClosedUnderApplication = thm $ do
    lab ascendingRegionIsClosedUnderApplicationLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", monotonic, " ", function]
    ma $ fa (a ∈ x) $ x ∈ asc f ⇒ f_ x ∈ asc f

    proof $ do
        s ["Let ", m a, " be an element of ", m $ asc f]
        s ["Because ", m $ a ⊆: f_ a, " holds, and because ", m f, " is monotonic, ", m $ f_ a ⊆: f_ (f_ a), " must also hold"]
        s ["This means that ", m $ f_ a, " is in the ascending region"]
  where
    f = funrel_
    f_ = fn f
    a = "x"
    x = posetset_

descendingRegionIsClosedUnderApplicationLabel :: Label
descendingRegionIsClosedUnderApplicationLabel = Label Theorem "descending-region-is-closed-under-application"

descendingRegionIsClosedUnderApplication :: Note
descendingRegionIsClosedUnderApplication = thm $ do
    lab descendingRegionIsClosedUnderApplicationLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", monotonic, " ", function]
    ma $ fa (a ∈ x) $ x ∈ desc f ⇒ f_ x ∈ desc f

    proof $ do
        s ["Let ", m a, " be an element of ", m $ desc f]
        s ["Because ", m $ f_ a ⊆: a, " holds, and because ", m f, " is monotonic, ", m $ f_ (f_ a) ⊆: f_ a, " must also hold"]
        s ["This means that ", m $ f_ a, " is in the descending region"]
  where
    f = funrel_
    f_ = fn f
    a = "x"
    x = posetset_

topInDescendingRegionLabel :: Label
topInDescendingRegionLabel = Label Theorem "top-element-is-in-descending-region"

topInDescendingRegion :: Note
topInDescendingRegion = thm $ do
    lab topInDescendingRegionLabel
    s ["Let ", m lat_, " be a ", boundedLattice_, " and let ", m $ fun f x x, " a ", monotonic, " ", function]
    ma $ bot ∈ asc f

    proof $ do
        s [m $ f_ bot, " is an element of ", m x, " and must therefore have the property ", m $ bot ⊆: f_ bot]
        s ["This means that ", m bot, " is an element of the ascending region"]
  where
    f_ = fn f
    f = funrel_
    x = latset_

botInAscendingRegionLabel :: Label
botInAscendingRegionLabel = Label Theorem "bot-element-is-in-ascending-region"

botInAscendingRegion :: Note
botInAscendingRegion = thm $ do
    lab botInAscendingRegionLabel
    s ["Let ", m lat_, " be a ", boundedLattice_, " and let ", m $ fun f x x, " a ", monotonic, " ", function]
    ma $ top ∈ desc f

    proof $ do
        s [m $ f_ top, " is an element of ", m x, " and must therefore have the property ", m $ f_ top ⊆: top]
        s ["This means that ", m top, " is an element of the descending region"]
  where
    f_ = fn f
    f = funrel_
    x = latset_


fixedPointRegionIsIntersectionOfAscAndDescLabel :: Label
fixedPointRegionIsIntersectionOfAscAndDescLabel = Label Theorem "fixed-point-region-is-intersection-of-ascending-region-and-descending-region"

fixedPointRegionIsIntersectionOfAscAndDesc :: Note
fixedPointRegionIsIntersectionOfAscAndDesc = thm $ do
    lab fixedPointRegionIsIntersectionOfAscAndDescLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", monotonic, " ", function]
    ma $ fix f =: asc f ∩ desc f

    proof $ do
        noindent
        itemize $ do
            item $ do
                bsub
                newline

                s ["Let ", m a, " be an element of ", m $ fix f]
                s ["By definition of ", m $ fix f, ", ", m $ f_ a, " is equal to ", m a]
                s ["Because ", m partord_, is, reflexive_, ref partialOrderDefinitionLabel, ref preorderDefinitionLabel, ", ", m $ a ⊆: a, " must hold"]
                s ["This means that ", m a, " is both an element of ", m $ asc f, " and of ", m $ desc f, " and therefore in their intersection"]

            item $ do
                bsup
                newline

                s ["Let ", m a, " be an element of both ", m $ asc f, and, m $ desc f]
                s ["This means that both ", m $ a ⊆: f_ a, and, m $ f_ a ⊆: a, " hold"]
                s ["Because ", m partord_, is, antisymmetric_, ", that means that ", m a, " equals ", m $ f_ a, " which entails that ", m a, " is a fixed point of ", m f]


  where
    f = funrel_
    f_ = fn f
    a = "a"
    x = posetset_

kleeneChainDefinition :: Note
kleeneChainDefinition = de $ do
    lab kleeneChainDefinitionLabel
    s ["Let ",  m lat_, " be a ", lattice_, and, m $ fun f x x, " a ", scottContinuous, " function"]
    s ["The ", kleeneChain', " starting at a point ", m $ a ∈ x, " is the set ", m $ kleeneCh a]
    ma $ kleeneCh a === setcmpr (i ∈ naturals) (f !: i `fn` x)
  where
    i = "i"
    f = funrel_
    a = "x"
    x = latset_

kleenesFixedPointTheorem :: Note
kleenesFixedPointTheorem = do
    thm $ do
        term "Kleene's fixed point theorem"
        newline
        s ["Let ", m lat_, " be a ", completeLattice_, and, m $ fun f x x, " a ", scottContinuous, " function"]
        ma $ lfp f =: sup (kleeneCh bot)

        toprove
    nte $ do
        s ["This gives us an algorithm to compute the least fixed point."]
        s ["Repeatedly applying ", m f, " to bot until we find a fixed point is enough to find ", m $ lfp f]
  where
    f = funrel_
    x = latset_












