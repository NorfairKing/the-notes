module Relations.Orders where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Sets.Basics.Terms
import           Sets.PointedSets.Macro

import           Relations.Basics.Macro
import           Relations.Basics.Terms
import           Relations.Equivalence.Macro
import           Relations.Equivalence.Terms
import           Relations.Preorders.Macro
import           Relations.Preorders.Terms

import           Relations.Orders.Macro
import           Relations.Orders.Terms

orders :: Note
orders = section "Orders" $ do
    nocite orderTheoryForComputerScientists

    antisymmetricDefinition

    subsection "Partial orders" $ do
        partialOrderDefinition
        posetDefinition
        crossPosetLift
        powsetPosetPreorder
        partialOrdersFromPreorders

    subsection "Total orders" $ do
        totalOrderDefinition

    subsection "Extremes" $ do
        greatestElementDefinition
        smallestElementDefinition

        maximalElementDefinition
        minimalElementDefinition

        upperBoundDefinition
        lowerBoundDefinition

        infimumDefinition
        supremumDefinition

        uniqueBounds

    subsection "Lattices" $ do
        meetSemilatticeDefinition
        joinSemilatticeDefinition
        latticeDefinition
        latticeExamples
        boundedLatticeDefinition
        crossLatticeLift
        completeLatticeDefinition
        completeLatticeIsBounded

        pointedLatticeDefinitions
        flatLatticeDefinition


antisymmetricDefinition :: Note
antisymmetricDefinition = de $ do
    lab antisymmetricDefinitionLabel
    s ["Let ", m xx, " be a set and ", m eqrel_, " an ", equivalenceRelation_, on , m xx]
    s ["Let ", m rel_, " be a binary ", relation, on, m xx]
    s [m rel_, " is called ", antisymmetric', " if it has the following property"]
    ma $ fa (cs [a, b] ∈ xx) ((pars $ (a `elem_` b) ∧ (b `elem_` a)) ⇒ (a .~ b))
  where
    a = "a"
    b = "b"
    xx = "X"

partialOrderDefinition :: Note
partialOrderDefinition = de $ do
    lab partialOrderDefinitionLabel
    s ["A ", partialOrder', " is an ", antisymmetric, " ", preorder_]

powsetPosetPreorder :: Note
powsetPosetPreorder = do
    thm $ do
        lab powersetPosetInducesPreorderTheoremLabel
        s ["Let ", m relposet_, " be a poset"]
        s [m $ relpreord (powset posetset_) partord_, ", where ", m partord_, " is defined as follows, is a ", preorder_]
        ma $ p ⊆: q ⇔ (fa (x ∈ p) $ te (y ∈ q) $ x ⊆: y)

        toprove
    cex $ do
        s ["In general, this preorder is not a partial order"]
        proof $ do
            s ["Consider sets of natural numbers with the natural total order."]
            ma $ setofs [1, 2, 3] ⊆: setof 3 <> quad <> text "and" <> quad <> setof 3 ⊆: setofs [1, 2, 3] <> quad <> text "but" <> quad <> setof 3 =§/= setofs [1, 2, 3]
            s ["This violates antisymmetry"]
  where
    x = "x"
    y = "y"
    p = "P"
    q = "Q"

partialOrdersFromPreorders :: Note
partialOrdersFromPreorders = thm $ do
    lab partialOrdersFromPreordersTheoremLabel
    s ["Given a preordered set ", m relpreord_, ", it is possible to lift the ", preorder, " ", m preord_, " to a ", partialOrder, " ", m $ relposet (eqcls_ preordset_) partord_]
    s ["Here, ", m eqrel_, " is defined naturally"]
    ma $ x .~ y ⇔ (x ⊆: y ∧ y ⊆: x)
    s [m partord_, " is then defined accross equivalence classes"]
    ma $ eqcl_ x ⊆: eqcl_ y ⇔ x ⊆: y

    toprove_ "This is in fact a partial order"
  where
    x = "x"
    y = "y"


posetDefinition :: Note
posetDefinition = de $ do
    lab posetDefinitionLabel
    s ["A ", term "partially ordered set", or, poset', " is a tuple ", m relposet_, " of a set and a partial order on that set"]


crossPosetLift :: Note
crossPosetLift = thm $ do
    lab crossproductLiftedPosetTheoremLabel
    s ["Let ", m $ list (relposet (x !: 1) (o !: 1)) (relposet (x !: 2) (o !: 2)) (relposet (x !: n) (o !: n)), " be ", poset, "s"]
    s [m cps, " is a ", poset, " where ", m o, " is defined as follows"]
    ma $ a ⊆: b ⇔ fa i (a !: i `oi` b !: i)

    proof $ do
        s ["We prove that ", m o, "is", reflexive, antisymmetric, and, transitive]
        itemize $ do
            item $ do
                s ["Let", m $ list (a !: 1) (a !: 2) (a !: n), "be n elements respectively of the sets", m $ list (x !: 1) (x !: 2) (x !: n)]
                s ["Because every ", m $ oi "" "", "is", reflexive, ", the following holds"]
                ma $ a !: i `oi` a !: i
                let e = tuplelist (a !: 1) (a !: 2) (a !: n)
                s ["This means that", m $ e ⊆: e, "holds and therefore that", m o, "is", reflexive]
            item $ do
                s ["Let", m $ list (a !: 1) (a !: 2) (a !: n), and, m $ list (b !: 1) (b !: 2) (b !: n), "be n elements respectively of the sets", m $ list (x !: 1) (x !: 2) (x !: n), "such that the following holds"]
                ma $ fa i $ a !: i `oi` b !: i  ∧  b !: i `oi` a !: i
                s ["Because every", m $ oi "" "", "is", antisymmetric, ", this implies the following"]
                ma $ fa i $ a !: i =: b !: i
                let ea = tuplelist (a !: 1) (a !: 2) (a !: n)
                let eb = tuplelist (b !: 1) (b !: 2) (b !: n)
                s ["This exactly means that ", m $ ea =: eb, "holds"]
                s ["Because", m o, "is", reflexive, ", this means that", m $ ea ⊆: eb, "holds"]
                s ["This proves that", m o, "is", antisymmetric]
            item $ do
                s ["Let", m $ list (a !: 1) (a !: 2) (a !: n), m $ list (b !: 1) (b !: 2) (b !: n), m $ list (c !: 1) (c !: 2) (c !: n), "be n elements respectively of the sets", m $ list (x !: 1) (x !: 2) (x !: n), "such that the following holds"]
                ma $ fa i $ a !: i `oi` b !: i ∧ b !: i `oi` c !: i
                s ["Because every", m $ oi "" "", "is", transitive, ", this implies the following"]
                ma $ fa i $ a !: i `oi` c !: i
                let ea = tuplelist (a !: 1) (a !: 2) (a !: n)
                let ec = tuplelist (c !: 1) (c !: 2) (c !: n)
                s ["As such,", m $ ea ⊆: ec, "also holds and therefore", m o, "is transitive"]
  where
    cps = relposet cp o
    cp = (x !: 1) ⨯ (x !: 2) ⨯ dotsb ⨯ (x !: n)
    a = "a"
    b = "b"
    c = "c"
    i = "i"
    o = partord_
    oi = binop $ raw "\\ " <> o !: "i" <> raw "\\ "
    x = posetset_
    n = "n"


totalOrderDefinition :: Note
totalOrderDefinition = de $ do
    s ["A ", totalOrder', " is a binary relation that is ", total_, ", ", transitive_, and, antisymmetric]


psDec :: Note
psDec = s ["Let ", m relposet_, " be a ", poset]

greatestElementDefinition :: Note
greatestElementDefinition = de $ do
    lab greatestElementDefinitionLabel
    psDec
    s ["A ", greatestElement', " ", m (a ∈ posetset_), " is an element such that all other elements are smaller"]
    ma $ fa (x ∈ posetset_) (x ⊆: a)
  where
    x = "x"
    a = "a"

smallestElementDefinition :: Note
smallestElementDefinition = de $ do
    lab smallestElementDefinitionLabel
    psDec
    s ["A ", smallestElement', " ", m (a ∈ posetset_), " is an element such that all other elements are greater"]
    ma $ fa (x ∈ posetset_) (a ⊆: x)
  where
    x = "x"
    a = "a"


maximalElementDefinition :: Note
maximalElementDefinition = de $ do
    lab maximalElementDefinitionLabel
    psDec
    s ["A ", maximalElement', " ", m (a ∈ posetset_), " is an element such that there exists no greater element"]
    ma $ not $ te (x ∈ posetset_) (a ⊆: x)
  where
    x = "x"
    a = "a"

minimalElementDefinition :: Note
minimalElementDefinition = de $ do
    lab minimalElementDefinitionLabel
    psDec
    s ["A ", minimalElement', " ", m (a ∈ posetset_), " is an element such that there exists no greater element"]
    ma $ not $ te (x ∈ posetset_) (a ⊆: x)
  where
    x = "x"
    a = "a"


upperBoundDefinition :: Note
upperBoundDefinition = de $ do
    lab upperBoundDefinitionLabel
    psDec
    s ["An ", upperBound', " ", m a, " is an element (not necessarily in ", m posetset_, ") that is greater than every element in ", m posetset_]
    ma $ fa (x ∈ posetset_) (x ⊆: a)
  where
    x = "x"
    a = "a"

lowerBoundDefinition :: Note
lowerBoundDefinition = de $ do
    lab lowerBoundDefinitionLabel
    psDec
    s ["An ", lowerBound', " ", m a, " is an element (not necessarily in ", m posetset_, ") that is smaller than every element in ", m posetset_]
    ma $ fa (x ∈ posetset_) (a ⊆: x)
  where
    x = "x"
    a = "a"

supremumDefinition :: Note
supremumDefinition = de $ do
    lab supremumDefinitionLabel
    lab joinDefinitionLabel
    psDec
    s ["A ", supremum', or, join', " of ", m posetset_, " is a smallest ", upperBound, " of ", m posetset_]
    s ["That is to say, all other upper bounds of ", m posetset_, " are larger"]
    ma $ sup posetset_ =: supcomp "" posetset_
    s [m $ a ⊔ b, "is the notation for the", supremum, "of two element"]
  where
    a = "a"
    b = "b"

infimumDefinition :: Note
infimumDefinition = de $ do
    lab infimumDefinitionLabel
    lab meetDefinitionLabel
    psDec
    s ["A ", infimum', or, meet', " of ", m posetset_, " is a greatest ", lowerBound, " of ", m posetset_]
    s ["That is to say, all other lower bounds of ", m posetset_, " are smaller"]
    ma $ inf posetset_ =: infcomp "" posetset_
    s [m $ a ⊓ b, "is the notation for the", infimum, "of two element"]
  where
    a = "a"
    b = "b"

uniqueBounds :: Note
uniqueBounds = thm $ do
    s ["If an supremum/infimum exists for a poset ", m relposet_, ", then it is unique"]
    -- TODO: maximal elements are greatest elements in totally ordered sets

    toprove

meetSemilatticeDefinition :: Note
meetSemilatticeDefinition = de $ do
    lab meetSemilatticeDefinitionLabel
    s ["A ", meetSemilattice', " is a ", poset, " ", m relposet_, " for which any two elements ", m a, and, m b, " have an ", infimum, " ", m (a ⊓ b), " as follows"]
    itemize $ do
        item $ m $ ((a ⊓ b) ⊆: a) ∧ ((a ⊓ b) ⊆: b)
        item $ m $ fa (c ∈ posetset_) $ ((c ⊆: a) ∧ (c ⊆: b)) ⇒ (c ⊆: (a ⊓ b))
  where
    a = "a"
    b = "b"
    c = "c"

joinSemilatticeDefinition :: Note
joinSemilatticeDefinition = de $ do
    lab joinSemilatticeDefinitionLabel
    s ["A ", joinSemilattice', " is a ", poset, " ", m relposet_, " for which any two elements ", m a, and, m b, " have a ", supremum, " ", m (a ⊔ b), " as follows"]
    itemize $ do
        item $ m $ (a ⊆: (a ⊔ b)) ∧ (b ⊆: (a ⊔ b))
        item $ m $ fa (c ∈ posetset_) $ ((a ⊆: c) ∧ (b ⊆: c)) ⇒ ((a ⊔ b) ⊆: c)
  where
    a = "a"
    b = "b"
    c = "c"

latticeDefinition :: Note
latticeDefinition = de $ do
    lab latticeDefinitionLabel
    s ["If a ", poset, " is both a ", meetSemilattice, " and a ", joinSemilattice, ", it is called a ", lattice']

latticeExamples :: Note
latticeExamples = do
    ex $ do
        s ["Let ", m ss, " be a set"]
        s [m $ lat (powset ss) subseteq_, " is a lattice"]
        toprove
  where
    ss = "S"

crossLatticeLift :: Note
crossLatticeLift = thm $ do
    lab crossproductLiftedLatticeTheoremLabel
    s ["Let ", m $ list (relposet (x !: 1) (o !: 1)) (relposet (x !: 2) (o !: 2)) (relposet (x !: n) (o !: n)), " be ", lattice, "s"]
    s ["The poset ", m $ relposet ((x !: 1) ⨯ (x !: 2) ⨯ dotsb ⨯ (x !: n)) o, ref crossproductLiftedPosetTheoremLabel, " is a ", lattice, " where the following properties hold"]

    ma $ do
        a ⊔ b =: supcomp i (a !: i ⊔ b !: i)
        quad <> text "and" <> quad
        a ⊓ b =: infcomp i (a !: i ⊓ b !: i)
    ma $ do
        top =: tuplelist (top !: (x !: 1)) (top !: (x !: 2)) (top !: (x !: n))
        quad <> text "and" <> quad
        bot =: tuplelist (bot !: (x !: 1)) (bot !: (x !: 2)) (bot !: (x !: n))

    toprove

  where
    a = "a"
    b = "b"
    o = partord_
    x = posetset_
    i = "i"
    n = "n"

boundedLatticeDefinition :: Note
boundedLatticeDefinition = de $ do
    lab boundedLatticeDefinitionLabel
    s ["A ", lattice, m relposet_, " is called a ", boundedLattice', " if there exists both a ", maximalElement, " ", m top, " and a ", minimalElement, " ", m bot, " in ", m posetset_, " as follows"]
    ma $ fa (x ∈ posetset_) $ (x ⊆: top) ∧ (bot ⊆: x)
  where
    x = "x"

completeLatticeDefinition :: Note
completeLatticeDefinition = de $ do
    lab completeLatticeDefinitionLabel
    s ["A " , lattice, m relposet_, " is called a ", completeLattice', " if every (possibly infinite) subset ", m l, " of ", m (posetset_), " has an ", infimum, " ", m (inf l), " and a ", supremum, " ", m (sup l)]
  where
    l = "L"

completeLatticeIsBounded :: Note
completeLatticeIsBounded = thm $ do
    s ["Every ", completeLattice, m relposet_, " is a ", boundedLattice, " where the ", maximalElement, " is the ", supremum, " of ", m posetset_, " and the ", minimalElement, " is the ", infimum, " of ", m posetset_]

    toprove

pointedLatticeDefinitions :: Note
pointedLatticeDefinitions = de $ do
    s ["Let ", m latset_, " be a ", set]
    s [m latset_, " can be lifted to be a ", poset, " ", m $ pset latset_ bot, " by adding a ", m bot, " ", element, or, " ", m $ pset latset_ top, " by adding a ", m top, " ", element]
    ma $ pset (latset_ !: bot) bot <> quad <> pset (latset_ ^: top) top
    s ["The ", partialOrder, "s ", m (partord_ !: pset (latset_ !: bot) bot), and, m (partord_ !: pset (latset_ ^: top) top), " are then defined as follows"]
    ma $ do
        partord_ !: pset (latset_ !: bot) bot =: setcmpr (tuple bot x) (x ∈ latset_)
        quad
        text "and"
        quad
        partord_ !: pset (latset_ ^: top) top =: setcmpr (tuple x top) (x ∈ latset_)

  where
    x = "x"

flatLatticeDefinition :: Note
flatLatticeDefinition = de $ do
    s ["Let ", m latset_, " be a ", set]
    s [m latset_, " can be lifted to be a so-called ", flatLattice', m $ lat xs partord_, " by defining the ", partialOrder, " ", m partord_, " as follows"]
    ma $ partord_ =: setcmpr (tuple top x) (x ∈ xs) ∪ setcmpr (tuple bot x) (x ∈ xs) ∪ setcmpr (tuple x x) (x ∈ xs)
  where
    x = "x"
    xs = latset_ .!: bot .^: top

orderTheoryForComputerScientists :: Reference
orderTheoryForComputerScientists = makeReference online "order-theory-for-computer-scientists" $
    [
        ("author", "Matt Might")
      , ("title", "Order theory for computer scientists")
      , ("year", "2012")
      , ("url", "http://http://matt.might.net/articles/partial-orders/")
      , ("urldate", "2015-10-13")
    ]
















