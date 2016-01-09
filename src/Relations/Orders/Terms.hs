module Relations.Orders.Terms where

import           Notes

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
    , "flat lattice"
    ]

makeThms [
      "Powerset poset induces preorder"
    , "Partial orders from preorders"
    , "Crossproduct lifted poset"
    , "Crossproduct lifted lattice"
    ]
