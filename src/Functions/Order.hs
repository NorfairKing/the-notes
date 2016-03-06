module Functions.Order where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Relations.Basics.Terms
import           Relations.Orders.Hasse
import           Relations.Orders.Macro
import           Relations.Orders.Terms
import           Relations.Preorders.Terms
import           Sets.Basics.Terms
import           Sets.Powerset.Terms

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Composition.Macro
import           Functions.Composition.Terms
import           Functions.Jections.Terms
import           Functions.Order.Diagrams

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

    tarskiFixedPointTheorem

    kleeneChainDefinition
    kleenesFixedPointTheorem

    latticesOverFunctions

    galoisConnectionS


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

galoisConnectionS :: Note
galoisConnectionS = subsection "Galois connections" $ do
    galoisConnectionDefinition
    galoisConnectionEquivalentDefinition
    galoisConnectionExamples
    galoisInsertionDefinition
    galoisInsertionOtherJections
    galoisConnectionsCompose



monotonicDefinition :: Note
monotonicDefinition = de $ do
    lab monotonicDefinitionLabel
    lab monotoneDefinitionLabel
    lab isotoneDefinitionLabel
    lab orderPreservingDefinitionLabel
    s ["Let ", m $ relposet x rx, and, m $ relposet y ry, " each be a ", poset_, and, m $ fun f x y, " a function"]
    s [m $ fun f x y, " is said to be ", monotonic' <> "," , monotone' <> ",", isotone', or, orderPreserving', " if it has the following property"]
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
    s [the, leastFixedPoint', m $ lfp f, "of", m f, "is a", fixedPoint, "such that the following holds"]
    let a = "a"
    ma $ fa (a ∈ x) $ (a =: (fn f a)) ⇒ lfp f ⊆: a
  where
    f = fun_
    x = posetset_


greatestFixedPointDefinition :: Note
greatestFixedPointDefinition = de $ do
    lab greatestFixedPointDefinitionLabel
    s ["Let ", m relposet_, " be a ", poset_, and, m $ fun f x x, " a ", function]
    s [the, greatestFixedPoint', m $ lfp f, "of", m f, "is a", fixedPoint, "such that the following holds"]
    let a = "a"
    ma $ fa (a ∈ x) $ (a =: (fn f a)) ⇒ a ⊆: gfp f
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

tarskiFixedPointTheorem :: Note
tarskiFixedPointTheorem = thm $ do
    term "Tarksi's fixed point theorem"
    newline
    s ["Let", m lat_, "be a", completeLattice_, "and let", m $ fun f x x, "be a", monotone, function]
    s [the, fixedPointRegion, m $ fix f, "of", m f, "is a", completeLattice]
    s ["Consequently, ", m f, "has a", greatestFixedPoint_, "and a", leastFixedPoint_]

    toprove
  where
    f = fun_
    x = latset_

kleeneChainDefinition :: Note
kleeneChainDefinition = de $ do
    lab kleeneChainDefinitionLabel
    s ["Let ",  m lat_, " be a ", lattice_, and, m $ fun f x x, " a ", scottContinuous, " function"]
    s [the , kleeneChain', " starting at a point ", m $ a ∈ x, " is the set ", m $ kleeneCh a]
    ma $ kleeneCh a === setcmpr (i ∈ naturals) (f ^: i `fn` x)
    s [the, kleeneChain, "is sometimes also called the", set, "of", functionIterates]
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



galoisConnectionDefinition :: Note
galoisConnectionDefinition = de $ do
    lab galoisConnectionDefinitionLabel
    lab reductiveDefinitionLabel
    lab extensiveDefinitionLabel
    s ["Let", m $ lat x rx, and, m $ lat y ry, "be", completeLattices]
    s ["Let", m $ fun a x y, and, m $ fun g y x, "be", monotone, functions]
    s [m a, and, m g, "form a", galoisConnection', "if the following hold"]
    itemize $ do
        item $ s [m $ a ● g, "is", reductive' <> ":", m $ fa (y_ ∈ y) $ inposet ry (fn a (fn g y_)) y_]
        item $ s [m $ g ● a, "is", extensive' <> ":", m $ fa (x_ ∈ x) $ inposet rx x_ (fn g (fn a x_))]
    s ["This is denoted as follows"]
    ma $ gcon a g (lat x rx) (lat y ry)
  where
    a = alpha
    g = gamma
    x = "X"
    x_ = "x"
    rx = partord_ !: x
    y = "Y"
    y_ = "y"
    ry = partord_ !: y

galoisConnectionEquivalentDefinition :: Note
galoisConnectionEquivalentDefinition = thm $ do
    s ["The following is an equilavent definition of a", galoisConnection]
    newline

    s ["Let", m $ lat x rx, and, m $ lat y ry, "be", completeLattices]
    s ["Let", m $ fun a x y, and, m $ fun g y x, "be", monotone, functions]
    s [m a, and, m g, "form a", galoisConnection', "if the following hold"]
    ma $ fa (x_ ∈ x) $ fa (y_ ∈ y) $ inposet ry (fn a x_) y_ ⇔ inposet rx x_ (fn g y_)

    toprove
  where
    a = alpha
    g = gamma
    x = "X"
    x_ = "x"
    rx = partord_ !: x
    y = "Y"
    y_ = "y"
    ry = partord_ !: y

galoisConnectionExamples :: Note
galoisConnectionExamples = do
    let c1 = "red"
        c2 = "blue"
    s ["In the following examples, the", raw c1, "arrows correspond to", m alpha, "and the", raw c2, "arrows correspond to", m gamma]
    ex $ do
        s ["The following diagrams shows a simple non-trivial", galoisConnection]
        let (a, b, c) = ("a", "b", "c")
            hd1 = hasseDiagram [a, c] [(a, c)]
            hd2 = hasseDiagram [b] []
            fun1 = [(a, b), (c, b)]
            fun2 = [(b, c)]
        orderFunctionFig 3 dotsConfig $ OrderFunctionFig
            [("A", hd1), ("B", hd2)]
            [(c1, fun1), (c2, fun2)]
    ex $ do
        s ["The following diagrams shows another simple non-trivial", galoisConnection]
        let (a, b, c, d) = ("a", "b", "c", "d")
            hd1 = hasseDiagram [a, c] [(a, c)]
            hd2 = hasseDiagram [b, d] [(b, d)]
            fun1 = [(a, b), (c, b)]
            fun2 = [(b, c), (d, c)]
        orderFunctionFig 4 dotsConfig $ OrderFunctionFig
            [("A", hd1), ("B", hd2)]
            [(c1, fun1), (c2, fun2)]
    ex $ do
        s ["The following diagram shows a", galoisConnection, "between two", posets]
        s ["One", poset, "is a", subset, "of the", powerset, "of", m integers]
        s ["The other is the set of information we can have about the sign of an integer"]
        s ["top means it could be anything, bot means it's impossible for this situation to occur, + means that the sign is positive and - means that the sign is negative"]
        let hd1 = hasseDiagram [all1, pos1, neg1, zp1, zm1, zero1, none] [(none, zero1), (zero1, zm1), (zero1, zp1), (zp1, pos1), (zm1, neg1), (zero1, neg1), (zero1, pos1), (neg1, all1), (pos1, all1)]
            hd2 = hasseDiagram [all2, pos2, neg2, zero2] [(zero2, neg2), (zero2, pos2), (neg2, all2), (pos2, all2)]
            fun1 = [(none, zero2), (zero1, pos2), (zp1, pos2), (zm1, neg2), (neg1, neg2), (pos1, pos2), (all1, all2)]
            fun2 = [(zero2, none), (neg2, neg1), (pos2, pos1), (all2, all1)]
            all1 = "{..., -1, 0, 1, ...}"
            pos1 = "{0, 1, ...}"
            neg1 = "{... -1, 0}"
            zm1 = "{-1, 0}"
            zp1 = "{0, 1}"
            zero1 = "{0}"
            none = "{}"
            all2 = "top"
            pos2 = "+"
            neg2 = "-"
            zero2 = "bot"
        orderFunctionFig 8 normalConfig $ OrderFunctionFig
            [("Concrete", hd1), ("Abstract", hd2)]
            [(c1, fun1), (c2, fun2)]


galoisInsertionDefinition :: Note
galoisInsertionDefinition = de $ do
    lab galoisInsertionDefinitionLabel
    s ["Let", m a, and, m g, "form a", galoisConnection]
    s ["This", galoisConnection, "is called a", galoisInsertion', "if", m g, "is", injective]
    s ["This is denoted as follows"]
    ma $ gins a g (lat x rx) (lat y ry)
  where
    a = alpha
    g = gamma
    x = "X"
    rx = partord_ !: x
    y = "Y"
    ry = partord_ !: y

galoisInsertionOtherJections :: Note
galoisInsertionOtherJections = thm $ do
    s ["Let", m a, and, m g, "form a", galoisInsertion]
    s [m a, "is", surjective, and, m $ a ● g, "is the identity", function]

    toprove
  where
    a = alpha
    g = gamma

galoisConnectionsCompose :: Note
galoisConnectionsCompose = thm $ do
    s ["Let", m a1, and, m g1 <> ", as well as", m a2, and, m g2, "form", galoisConnections]
    ma $ gcon a1 g1 (lat x rx) (lat y ry)
    ma $ gcon a2 g2 (lat y ry) (lat z rz)
    s [m (a2 ● a1), and, m (g1 ● g2), "then form a", galoisConnection]
    ma $ gcon (a2 ● a1) (g1 ● g2) (lat x rx) (lat z rz)

    toprove
  where
    a = alpha
    a1 = a !: 1
    a2 = a !: 2
    g = gamma
    g1 = g !: 1
    g2 = g !: 2
    x = "X"
    rx = partord_ !: x
    y = "Y"
    ry = partord_ !: y
    z = "Z"
    rz = partord_ !: z
