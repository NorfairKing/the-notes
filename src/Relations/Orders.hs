module Relations.Orders where

import           Notes

import           Relations.Basics            (relation, total_, transitive_)
import           Relations.Equivalence       (equivalenceRelation_)
import           Relations.Preorders         (preorder, preorder_)

import           Sets.Basics

import           Sets.PointedSets.Macro

import           Relations.Basics.Macro
import           Relations.Equivalence.Macro
import           Relations.Orders.Macro
import           Relations.Preorders.Macro

makeDefs [
      "antisymmetric"
    , "partial order"
    , "total order"
    , "greatest element"
    , "smallest element"
    , "maximal element"
    , "minimal element"
    , "upper bound"
    , "lower bound"
    , "supremum", "join"
    , "infimum", "meet"
    , "meet semilattice"
    , "join semilattice"
    , "bounded lattice"
    , "complete lattice"
    , "poset"
    , "lattice"
    , "flat lattice"]

orders :: Note
orders = note "orders" $ do
    nocite orderTheoryForComputerScientists

    section "Orders"

    antisymmetricDefinition

    subsection "Partial orders"
    partialOrderDefinition
    posetDefinition
    crossPosetLift
    powsetPosetPreorder
    partialOrdersFromPreorders

    subsection "Total orders"
    totalOrderDefinition

    subsection "Extremes"
    greatestElementDefinition
    smallestElementDefinition

    maximalElementDefinition
    minimalElementDefinition

    upperBoundDefinition
    lowerBoundDefinition

    supremumDefinition
    infimumDefinition

    uniqueBounds

    subsection "Lattices"
    meetSemilatticeDefinition
    joinSemilatticeDefinition
    latticeDefinition
    latticeExamples
    crossLatticeLift
    boundedLatticeDefinition
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

powsetPosetPreorderLabel :: Label
powsetPosetPreorderLabel = Label Theorem "powerset-poset-induces-preorder"

powsetPosetPreorder :: Note
powsetPosetPreorder = do
    thm $ do
        lab powsetPosetPreorderLabel
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

partialOrdersFromPreordersLabel :: Label
partialOrdersFromPreordersLabel = Label Theorem "partial-orders-from-preorders"

partialOrdersFromPreorders :: Note
partialOrdersFromPreorders = thm $ do
    lab partialOrdersFromPreordersLabel
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

crossPosetLiftLabel :: Label
crossPosetLiftLabel = Label Theorem "cross-poset-lift"

crossPosetLift :: Note
crossPosetLift = thm $ do
    lab crossPosetLiftLabel
    s ["Let ", m $ list (relposet (x !: 1) (o !: 1)) (relposet (x !: 2) (o !: 2)) (relposet (x !: n) (o !: n)), " be ", poset, "s"]
    s [m $ relposet ((x !: 1) ⨯ (x !: 2) ⨯ dotsb ⨯ (x !: n)) o, " is a ", poset, " where ", m o, " is defined as follows"]
    ma $ a ⊆: b ⇔ fa i (a !: i `oi` b !: i)

    toprove

  where
    a = "a"
    b = "b"
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

infimumDefinition :: Note
infimumDefinition = de $ do
    lab infimumDefinitionLabel
    lab meetDefinitionLabel
    psDec
    s ["A ", infimum', or, meet', " of ", m posetset_, " is a greatest ", lowerBound, " of ", m posetset_]
    s ["That is to say, all other lower bounds of ", m posetset_, " are smaller"]

uniqueBounds :: Note
uniqueBounds = thm $ do
    s ["If an supremum/infimum exists for a poset ", m relposet_, ", then it is unique"]
    -- TODO: maximal elements are greatest elements in totally ordered sets

    toprove

meetSemilatticeDefinition :: Note
meetSemilatticeDefinition = de $ do
    lab meetSemilatticeDefinitionLabel
    s ["A ", meetSemilattice', " is a ", poset, " ", m relposet_, " for which any two elements ", m a, and, m b, " have an ", infimum, " ", m (a ⊔ b), " as follows"]
    itemize $ do
        item $ m $ ((a ⊔ b) ⊆: a) ∧ ((a ⊔ b) ⊆: b)
        item $ m $ fa (c ∈ posetset_) $ ((c ⊆: a) ∧ (c ⊆: b)) ⇒ (c ⊆: (a ⊔ b))
  where
    a = "a"
    b = "b"
    c = "c"

joinSemilatticeDefinition :: Note
joinSemilatticeDefinition = de $ do
    lab joinSemilatticeDefinitionLabel
    s ["A ", joinSemilattice', " is a ", poset, " ", m relposet_, " for which any two elements ", m a, and, m b, " have a ", supremum, " ", m (a ⊓ b), " as follows"]
    itemize $ do
        item $ m $ (a ⊆: (a ⊓ b)) ∧ (b ⊆: (a ⊓ b))
        item $ m $ fa (c ∈ posetset_) $ ((a ⊆: c) ∧ (b ⊆: c)) ⇒ ((a ⊓ b) ⊆: c)
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

crossLatticeLiftLabel :: Label
crossLatticeLiftLabel = Label Theorem "cross-lattice-lift"

crossLatticeLift :: Note
crossLatticeLift = thm $ do
    lab crossLatticeLiftLabel
    s ["Let ", m $ list (relposet (x !: 1) (o !: 1)) (relposet (x !: 2) (o !: 2)) (relposet (x !: n) (o !: n)), " be ", lattice, "s"]
    s ["The poset ", m $ relposet ((x !: 1) ⨯ (x !: 2) ⨯ dotsb ⨯ (x !: n)) o, ref crossPosetLiftLabel, " is a ", lattice, " where the following properties hold"]

    ma $ (a ⊔ b =: supcomp i (a !: i ⊔ b !: i)) <> quad <> text "and" <> quad <> (a ⊓ b =: infcomp i (a !: i ⊓ b !: i))
    ma $ (bot =: tuplelist (bot !: (x !: 1)) (bot !: (x !: 2)) (bot !: (x !: n)))  <> quad <> text "and" <> quad <> (top =: tuplelist (top !: (x !: 1)) (top !: (x !: 2)) (top !: (x !: n)))

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
    s ["A ", lattice, m relposet_, " is called a ", boundedLattice, " if there exists both a ", maximalElement, " ", m top, " and a ", minimalElement, " ", m bot, " in ", m posetset_, " as follows"]
    ma $ fa (x ∈ posetset_) $ (x ⊆: top) ∧ (bot ⊆: x)
  where
    x = "x"

completeLatticeDefinition :: Note
completeLatticeDefinition = de $ do
    lab completeLatticeDefinitionLabel
    s ["A " , lattice, m relposet_, " is called a ", completeLattice, " if every (possibly infinite) subset ", m l, " of ", m (posetset_), " has an ", infimum, " ", m (inf l), " and a ", supremum, " ", m (sup l)]
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
















