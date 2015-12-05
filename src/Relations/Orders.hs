module Relations.Orders where

import           Notes

import           Relations.BasicDefinitions (relation, total_, transitive_)
import           Relations.Equivalence      (equivalenceRelation_, preorder_)

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
    , "lattice"]

orders :: Notes
orders = notesPart "orders" body

body :: Note
body = do
    nocite orderTheoryForComputerScientists

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
    meetSemilatticeDefinition
    joinSemilatticeDefinition
    latticeDefinition
    boundedLatticeDefinition
    completeLatticeDefinition
    completeLatticeIsBounded


antisymmetricDefinition :: Note
antisymmetricDefinition = de $ do
    lab antisymmetricDefinitionLabel
    s ["Let ", m xx, " be a set and ", m eqrel, " an ", equivalenceRelation_, on , m xx]
    s ["Let ", m rel, " be a binary ", relation, on, m xx]
    s [m rel, " is called ", antisymmetric', " if it has the following property"]
    ma $ fa (cs [a, b] ∈ xx) ((pars $ (a `inrel` b) ∧ (b `inrel` a)) ⇒ (a .~ b))
  where
    a = "a"
    b = "b"
    xx = "X"

partialOrderDefinition :: Note
partialOrderDefinition = de $ do
  lab partialOrderDefinitionLabel
  s ["A ", partialOrder', " is an ", antisymmetric, " ", preorder_]

posetDefinition :: Note
posetDefinition = de $ do
    lab posetDefinitionLabel
    s ["A ", term "partially ordered set", or, poset', " is a tuple ", m relposet, " of a set and a partial order on that set"]

totalOrderDefinition :: Note
totalOrderDefinition = de $ do
    s ["A ", totalOrder', " is a binary relation that is ", total_, ", ", transitive_, and, antisymmetric]


psDec :: Note
psDec = s ["Let ", m relposet, " be a ", poset]

greatestElementDefinition :: Note
greatestElementDefinition = de $ do
    lab greatestElementDefinitionLabel
    psDec
    s ["A ", greatestElement', " ", m (a ∈ posetset), " is an element such that all other elements are smaller"]
    ma $ fa (x ∈ posetset) (x ⊆: a)
  where
    x = "x"
    a = "a"

smallestElementDefinition :: Note
smallestElementDefinition = de $ do
    lab smallestElementDefinitionLabel
    psDec
    s ["A ", smallestElement', " ", m (a ∈ posetset), " is an element such that all other elements are greater"]
    ma $ fa (x ∈ posetset) (a ⊆: x)
  where
    x = "x"
    a = "a"


maximalElementDefinition :: Note
maximalElementDefinition = de $ do
    lab maximalElementDefinitionLabel
    psDec
    s ["A ", maximalElement', " ", m (a ∈ posetset), " is an element such that there exists no greater element"]
    ma $ not $ te (x ∈ posetset) (a ⊆: x)
  where
    x = "x"
    a = "a"

minimalElementDefinition :: Note
minimalElementDefinition = de $ do
    lab minimalElementDefinitionLabel
    psDec
    s ["A ", minimalElement', " ", m (a ∈ posetset), " is an element such that there exists no greater element"]
    ma $ not $ te (x ∈ posetset) (a ⊆: x)
  where
    x = "x"
    a = "a"


upperBoundDefinition :: Note
upperBoundDefinition = de $ do
    lab upperBoundDefinitionLabel
    psDec
    s ["An ", upperBound', " ", m a, " is an element (not necessarily in ", m posetset, ") that is greater than every element in ", m posetset]
    ma $ fa (x ∈ posetset) (x ⊆: a)
  where
    x = "x"
    a = "a"

lowerBoundDefinition :: Note
lowerBoundDefinition = de $ do
    lab lowerBoundDefinitionLabel
    psDec
    s ["An ", lowerBound', " ", m a, " is an element (not necessarily in ", m posetset, ") that is smaller than every element in ", m posetset]
    ma $ fa (x ∈ posetset) (a ⊆: x)
  where
    x = "x"
    a = "a"

supremumDefinition :: Note
supremumDefinition = de $ do
    lab supremumDefinitionLabel
    lab joinDefinitionLabel
    psDec
    s ["A ", supremum', or, join', " of ", m posetset, " is a smallest ", upperBound, " of ", m posetset]
    s ["That is to say, all other upper bounds of ", m posetset, " are larger"]

infimumDefinition :: Note
infimumDefinition = de $ do
    lab infimumDefinitionLabel
    lab meetDefinitionLabel
    psDec
    s ["A ", infimum', or, meet', " of ", m posetset, " is a greatest ", lowerBound, " of ", m posetset]
    s ["That is to say, all other lower bounds of ", m posetset, " are smaller"]

uniqueBounds :: Note
uniqueBounds = thm $ do
    s ["If an supremum/infimum exists for a poset ", m relposet, ", then it is unique"]
    -- TODO: maximal elements are greatest elements in totally ordered sets

    toprove

meetSemilatticeDefinition :: Note
meetSemilatticeDefinition = de $ do
    lab meetSemilatticeDefinitionLabel
    s ["A ", meetSemilattice', " is a ", poset, " ", m relposet, " for which any two elements ", m a, and, m b, " have an ", infimum, " ", m (a ⊔ b), " as follows"]
    itemize $ do
        item $ m $ ((a ⊔ b) ⊆: a) ∧ ((a ⊔ b) ⊆: b)
        item $ m $ fa (c ∈ posetset) $ ((c ⊆: a) ∧ (c ⊆: b)) ⇒ (c ⊆: (a ⊔ b))
  where
    a = "a"
    b = "b"
    c = "c"

joinSemilatticeDefinition :: Note
joinSemilatticeDefinition = de $ do
    lab joinSemilatticeDefinitionLabel
    s ["A ", joinSemilattice', " is a ", poset, " ", m relposet, " for which any two elements ", m a, and, m b, " have a ", supremum, " ", m (a ⊓ b), " as follows"]
    itemize $ do
        item $ m $ (a ⊆: (a ⊓ b)) ∧ (b ⊆: (a ⊓ b))
        item $ m $ fa (c ∈ posetset) $ ((a ⊆: c) ∧ (b ⊆: c)) ⇒ ((a ⊓ b) ⊆: c)
  where
    a = "a"
    b = "b"
    c = "c"

latticeDefinition :: Note
latticeDefinition = de $ do
    lab latticeDefinitionLabel
    s ["If a ", poset, " is both a ", meetSemilattice, " and a ", joinSemilattice, ", it is called a ", lattice']

boundedLatticeDefinition :: Note
boundedLatticeDefinition = de $ do
    lab boundedLatticeDefinitionLabel
    s ["A ", lattice, m relposet, " is called a ", boundedLattice, " if there exists both a ", maximalElement, " ", m top, " and a ", minimalElement, " ", m bot, " in ", m posetset, " as follows"]
    ma $ fa (x ∈ posetset) $ (x ⊆: top) ∧ (bot ⊆: x)
  where
    x = "x"

completeLatticeDefinition :: Note
completeLatticeDefinition = de $ do
    lab completeLatticeDefinitionLabel
    s ["A " , lattice, m relposet, " is called a ", completeLattice, " if every (possibly infinite) subset ", m l, " of ", m (posetset), " has an ", infimum, " ", m (inf l), " and a ", supremum, " ", m (sup l)]
  where
    l = "L"

completeLatticeIsBounded :: Note
completeLatticeIsBounded = thm $ do
    s ["Every ", completeLattice, m relposet, " is a ", boundedLattice, " where the ", maximalElement, " is the ", supremum, " of ", m posetset, " and the ", minimalElement, " is the ", infimum, " of ", m posetset]

    toprove


orderTheoryForComputerScientists :: Reference
orderTheoryForComputerScientists = Reference online "order-theory-for-computer-scientists" $
    [
        ("author", "Matt Might")
      , ("title", "Order theory for computer scientists")
      , ("year", "2012")
      , ("url", "http://http://matt.might.net/articles/partial-orders/")
      , ("urldate", "2015-10-13")
    ]
















