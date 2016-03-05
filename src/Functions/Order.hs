module Functions.Order where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Relations.Basics.Terms
import           Relations.Orders.Macro
import           Relations.Orders.Terms
import           Relations.Preorders.Terms
import           Sets.Basics.Terms

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Composition.Macro
import           Functions.Composition.Terms

import           Functions.Order.Macro
import           Functions.Order.Terms

order :: Note
order = section "Functions and orders" $ do
    subsection "Monotonic functions" $ do
        monotonicDefinition
        monotonicFunctionsClosedUnderComposition

    scottContinuousDefinition
    fixedPointDefinition
    leastFixedPointDefinition
    greatestFixedPointDefinition
    regions

    kleeneChainDefinition
    kleenesFixedPointTheorem

    latticesOverFunctions


regions :: Note
regions = subsection "Regions" $ do
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
    lab monotoneDefinitionLabel
    s ["Let ", m $ relposet x rx, and, m $ relposet y ry, " each be a ", poset_, and, m $ fun f x y, " a function"]
    s [m $ fun f x y, " is said to be ", monotonic', or, monotone, " if it has the following property"]
    ma $ fa (cs [x1, x2] ∈ x) $ inposet rx x1 x2 ⇒ inposet ry (f_ x1) (f_ x2)
  where
    x1 = x !: 1
    x2 = x !: 2
    f = fun_
    f_ = fn f
    x = "X"
    rx = partord_ !: x
    y = "Y"
    ry = partord_ !: y

monotonicFunctionsClosedUnderComposition :: Note
monotonicFunctionsClosedUnderComposition = thm $ do
    lab monotonicFunctionsClosedUnderCompositionTheoremLabel
    s [the, composition, "of two", monotonic, functions, "is", monotonic]
    s ["Let ", m f1, and, m f2, "be", monotonic, functions]
    s [m $ f2 ● f1, "is a", monotonic, function]

    proof $ do
        let a = "A"
            b = "B"
            c = "C"
            ra = partord_ !: a
            rb = partord_ !: b
        s ["Let ", m $ fun f1 a b, and, m $ fun f2 b c, "be", monotonic, functions, "on the", posets, m $ relposet a ra, and, m $ relposet b rb]
        let x = "x"
            y = "y"
            oa = binop $ raw "\\ " <> partord_ !: "a" <> raw "\\ "
        s ["Let ", m x, and, m y, "be elements of", m a, and, m b, "respectively, such that the following holds"]
        ma $ x `oa` y
        let ob = binop $ raw "\\ " <> partord_ !: "b" <> raw "\\ "
        s ["Because ", m f1, "is", monotonic, "the following must hold as well"]
        ma $ fn f1 x `ob` fn f1 y
        s ["Because ", m f2, "is", monotonic, "the following must hold as well"]
        ma $ fn f2 (fn f1 x) `ob` fn f2 (fn f1 y)
        ma $ fn (pars $ f2 ● f1) x `ob` fn (pars $ f2 ● f1) y
        s ["This means that", m $ f2 ● f1, "is monotonic"]

  where
    f1 = fun_ !: 1
    f2 = fun_ !: 2

scottContinuousDefinition :: Note
scottContinuousDefinition = de $ do
    lab scottContinuousDefinitionLabel
    s ["Let ", m $ lat x rx, and, m $ lat y ry, " each be a ", lattice_, and, m $ fun f x y, " a function"]
    s [m $ fun fun_ x y, " is called ", scottContinuous', " if it has the following property"]
    ma $ fa (ss ⊆ x) $ f_ (sup ss) =: sup (f □ ss)
  where
    ss = "S"
    f = fun_
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
    f = fun_
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
    f = fun_
    x = posetset_


greatestFixedPointDefinition :: Note
greatestFixedPointDefinition = de $ do
    lab greatestFixedPointDefinitionLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", function]
    s ["The ", greatestFixedPoint', " ", m $ gfp f, " of ", m f, " is defined as follows"]
    ma $ gfp f === sup (fix f)
  where
    f = fun_
    x = posetset_

fixedPointRegionDefinition :: Note
fixedPointRegionDefinition = de $ do
    lab fixedPointRegionDefinitionLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", function]
    s ["The ", fixedPointRegion', " ", m $ fix f, " is the ", set, " of ", fixedPoint, "s of ", m latset_]
    ma $ fix f === setcmpr (a ∈ latset_) (a =: f_ a)
  where
    f = fun_
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
    f = fun_
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
    f = fun_
    f_ = fn f
    a = "x"
    x = posetset_

ascendingRegionIsClosedUnderApplication :: Note
ascendingRegionIsClosedUnderApplication = thm $ do
    lab ascendingRegionIsClosedUnderApplicationTheoremLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", monotonic, " ", function]
    ma $ fa (a ∈ x) $ x ∈ asc f ⇒ f_ x ∈ asc f

    proof $ do
        s ["Let ", m a, " be an element of ", m $ asc f]
        s ["Because ", m $ a ⊆: f_ a, " holds, and because ", m f, " is monotonic, ", m $ f_ a ⊆: f_ (f_ a), " must also hold"]
        s ["This means that ", m $ f_ a, " is in the ascending region"]
  where
    f = fun_
    f_ = fn f
    a = "x"
    x = posetset_

descendingRegionIsClosedUnderApplication :: Note
descendingRegionIsClosedUnderApplication = thm $ do
    lab descendingRegionIsClosedUnderApplicationTheoremLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", monotonic, " ", function]
    ma $ fa (a ∈ x) $ x ∈ desc f ⇒ f_ x ∈ desc f

    proof $ do
        s ["Let ", m a, " be an element of ", m $ desc f]
        s ["Because ", m $ f_ a ⊆: a, " holds, and because ", m f, " is monotonic, ", m $ f_ (f_ a) ⊆: f_ a, " must also hold"]
        s ["This means that ", m $ f_ a, " is in the descending region"]
  where
    f = fun_
    f_ = fn f
    a = "x"
    x = posetset_

topInDescendingRegion :: Note
topInDescendingRegion = thm $ do
    lab topElementIsInDescendingRegionTheoremLabel
    s ["Let ", m lat_, " be a ", boundedLattice_, " and let ", m $ fun f x x, " a ", monotonic, " ", function]
    ma $ bot ∈ asc f

    proof $ do
        s [m $ f_ bot, " is an element of ", m x, " and must therefore have the property ", m $ bot ⊆: f_ bot]
        s ["This means that ", m bot, " is an element of the ascending region"]
  where
    f_ = fn f
    f = fun_
    x = latset_

botInAscendingRegion :: Note
botInAscendingRegion = thm $ do
    lab bottomElementIsInAscendingRegionTheoremLabel
    s ["Let ", m lat_, " be a ", boundedLattice_, " and let ", m $ fun f x x, " a ", monotonic, " ", function]
    ma $ top ∈ desc f

    proof $ do
        s [m $ f_ top, " is an element of ", m x, " and must therefore have the property ", m $ f_ top ⊆: top]
        s ["This means that ", m top, " is an element of the descending region"]
  where
    f_ = fn f
    f = fun_
    x = latset_


fixedPointRegionIsIntersectionOfAscAndDesc :: Note
fixedPointRegionIsIntersectionOfAscAndDesc = thm $ do
    lab fixedPointRegionIsIntersectionOfAscendingRegionAndDescendingRegionTheoremLabel
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
    f = fun_
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
    f = fun_
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
    f = fun_
    x = latset_


latticesOverFunctions :: Note
latticesOverFunctions = thm $ do
    lab latticesOverFunctionsTheoremLabel
    s ["Let ", m lat_, " be a ", lattice, and, m y, " a set"]
    s [m $ lat (funt x y) partord_, " is a ", lattice, " where ", m partord_, " is defined as follows"]
    ma $ f ⊆: g ⇔ fa (a ∈ dom f) (f -: a ⊆: g -: a)
    s ["This also implies the following"]
    ma $ (pars $ f ⊔ g) -: a =: (f -: a ⊔  g -: a)
    ma $ (pars $ f ⊓ g) -: a =: (f -: a ⊓  g -: a)

    toprove
  where
    f = "f"
    g = "g"
    a = "a"
    x = latset_
    y = "Y"







