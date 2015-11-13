module Relations.Orders (
      orders

    , partialOrder
    , poset
    , totalOrder

    , greatestElement
    , smallestElement

    , maximalElement
    , minimalElement

    , upperBound
    , lowerBound

    , supremum, join
    , infimum, meet

    , meetSemilattice
    , joinSemilattice

    , lattice

    , boundedLattice
    , completeLattice
  ) where

import           Notes

import           Relations.BasicDefinitions (relation, total_, transitive_)
import           Relations.Equivalence      (equivalenceRelation_, preorder_)

orders :: Notes
orders = notesPart "orders" body

body :: Note
body = do
    section "Orders"

    antisymmetricDefinition

    subsection "Partial orders"
    partialOrderDefinition
    posetDefinition

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
    meetSemiLatticeDefinition
    joinSemiLatticeDefinition
    latticeDefinition
    boundedLatticeDefinition
    completeLatticeDefinition
    completeLatticeIsBounded



antisymmetric :: Note
antisymmetric = ix "antisymmetric"

antisymmetricDefinition :: Note
antisymmetricDefinition = de $ do
    s ["Let ", m xx, " be a set and ", m eqrel, " an ", equivalenceRelation_, on , m xx]
    s ["Let ", m rel, " be a binary ", relation, on, m xx]
    s [m rel, " is called ", term "antisymmetric", " if it has the following property"]
    ma $ fa (cs [a, b] ∈ xx) ((pars $ (a `inrel` b) ∧ (b `inrel` a)) ⇒ (a .~ b))
  where
    a = "a"
    b = "b"
    xx = "X"

partialOrder :: Note
partialOrder = ix "partial order"

partialOrderDefinition :: Note
partialOrderDefinition = de $ do
  s ["A ", term "partial order", " is an ", antisymmetric, " ", preorder_]

poset :: Note
poset = ix "poset"

posetDefinition :: Note
posetDefinition = de $ do
    s ["A ", term "partially ordered set", or, term "poset", " is a tuple ", m relposet, " of a set and a partial order on that set"]

totalOrder :: Note
totalOrder = ix "total order"

totalOrderDefinition :: Note
totalOrderDefinition = de $ do
    s ["A ", term "total order", " is a binary relation that is ", total_, ", ", transitive_, and, antisymmetric]


psDec :: Note
psDec = s ["Let ", m relposet, " be a ", poset]

greatestElement :: Note
greatestElement = ix "greatest element"

greatestElementDefinition :: Note
greatestElementDefinition = de $ do
    psDec
    s ["A ", term "greatest element", " ", m (a ∈ posetset), " is an element such that all other elements are smaller"]
    ma $ fa (x ∈ posetset) (x ⊆: a)
  where
    x = "x"
    a = "a"

smallestElement :: Note
smallestElement = ix "smallest element"

smallestElementDefinition :: Note
smallestElementDefinition = de $ do
    psDec
    s ["A ", term "smallest element", " ", m (a ∈ posetset), " is an element such that all other elements are greater"]
    ma $ fa (x ∈ posetset) (a ⊆: x)
  where
    x = "x"
    a = "a"


maximalElement :: Note
maximalElement = ix "maximal element"

maximalElementDefinition :: Note
maximalElementDefinition = de $ do
    psDec
    s ["A ", term "maximal element", " ", m (a ∈ posetset), " is an element such that there exists no greater element"]
    ma $ not $ te (x ∈ posetset) (a ⊆: x)
  where
    x = "x"
    a = "a"

minimalElement :: Note
minimalElement = ix "minimal element"

minimalElementDefinition :: Note
minimalElementDefinition = de $ do
    psDec
    s ["A ", term "minimal element", " ", m (a ∈ posetset), " is an element such that there exists no greater element"]
    ma $ not $ te (x ∈ posetset) (a ⊆: x)
  where
    x = "x"
    a = "a"


upperBound :: Note
upperBound = ix "upper bound"

upperBoundDefinition :: Note
upperBoundDefinition = de $ do
    psDec
    s ["An ", term "upper bound", " ", m a, " is an element (not necessarily in ", m posetset, ") that is greater than every element in ", m posetset]
    ma $ fa (x ∈ posetset) (x ⊆: a)
  where
    x = "x"
    a = "a"


lowerBound :: Note
lowerBound = ix "lower bound"

lowerBoundDefinition :: Note
lowerBoundDefinition = de $ do
    psDec
    s ["An ", term "lower bound", " ", m a, " is an element (not necessarily in ", m posetset, ") that is smaller than every element in ", m posetset]
    ma $ fa (x ∈ posetset) (a ⊆: x)
  where
    x = "x"
    a = "a"


supremum :: Note
supremum = ix "supremum"

join :: Note
join = ix "join"

supremumDefinition :: Note
supremumDefinition = de $ do
    psDec
    s ["A ", term "supremum", or, term "join", " of ", m posetset, " is a smallest upper bound of ", m posetset]
    s ["That is to say, all other upper bounds of ", m posetset, " are larger"]

infimum :: Note
infimum = ix "infimum"

meet :: Note
meet = ix "meet"

infimumDefinition :: Note
infimumDefinition = de $ do
    psDec
    s ["A ", term "infimum", or, term "meet", " of ", m posetset, " is a greatest lower bound of ", m posetset]
    s ["That is to say, all other lower bounds of ", m posetset, " are smaller"]

uniqueBounds :: Note
uniqueBounds = thm $ do
    s ["If an supremum/infimum exists for a poset ", m relposet, ", then it is unique"]
    -- TODO: maximal elements are greatest elements in totally ordered sets

    toprove

meetSemilattice :: Note
meetSemilattice = ix "meet semilattice"

meetSemiLatticeDefinition :: Note
meetSemiLatticeDefinition = de $ do
    s ["A ", term "meet semilattice", " is a ", poset, " ", m relposet, " for which any two elements ", m a, and, m b, " have an ", infimum, " ", m (a ⊔ b), " as follows"]
    itemize $ do
        item $ m $ ((a ⊔ b) ⊆: a) ∧ ((a ⊔ b) ⊆: b)
        item $ m $ fa (c ∈ posetset) $ ((c ⊆: a) ∧ (c ⊆: b)) ⇒ (c ⊆: (a ⊔ b))
  where
    a = "a"
    b = "b"
    c = "c"

joinSemilattice :: Note
joinSemilattice = ix "join semilattice"

joinSemiLatticeDefinition :: Note
joinSemiLatticeDefinition = de $ do
    s ["A ", term "join semilattice", " is a ", poset, " ", m relposet, " for which any two elements ", m a, and, m b, " have a ", supremum, " ", m (a ⊓ b), " as follows"]
    itemize $ do
        item $ m $ (a ⊆: (a ⊓ b)) ∧ (b ⊆: (a ⊓ b))
        item $ m $ fa (c ∈ posetset) $ ((a ⊆: c) ∧ (b ⊆: c)) ⇒ ((a ⊓ b) ⊆: c)
  where
    a = "a"
    b = "b"
    c = "c"

lattice :: Note
lattice = ix "lattice"

latticeDefinition :: Note
latticeDefinition = de $ do
    s ["If a ", poset, " is both a ", meetSemilattice, " and a ", joinSemilattice, ", it is called a ", term "lattice"]

boundedLattice :: Note
boundedLattice = ix "bounded lattice"

boundedLatticeDefinition :: Note
boundedLatticeDefinition = de $ do
    s ["A ", lattice, m relposet, " is called ", term "bounded", " if there exists both a ", maximalElement, " ", m top, " and a ", minimalElement, " ", m bot, " in ", m posetset, " as follows"]
    ma $ fa (x ∈ posetset) $ (x ⊆: top) ∧ (bot ⊆: x)
  where
    x = "x"

completeLattice :: Note
completeLattice = ix "complete lattice"

completeLatticeDefinition :: Note
completeLatticeDefinition = de $ do
    s ["A " , lattice, m relposet, " is called ", term "complete", " if every (possibly infinite) subset ", m l, " of ", m (posetset), " has an ", infimum, " ", m (inf l), " and a ", supremum, " ", m (sup l)]
  where
    l = "L"

completeLatticeIsBounded :: Note
completeLatticeIsBounded = thm $ do
    s ["Every ", completeLattice, m relposet, " is a ", boundedLattice, " where the ", maximalElement, " is the ", supremum, " of ", m posetset, " and the ", minimalElement, " is the ", infimum, " of ", m posetset]

    toprove



















