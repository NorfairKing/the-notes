module Relations.Orders.Terms where

import           Notes

makeDefs [
      "antisymmetric"
    , "partial order"
    , "comparable"
    , "incomparable"
    , "chain"
    , "height"
    , "antichain"
    , "width"
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
    , "total order"
    ]

makeThms [
      "Powerset poset induces preorder"
    , "Partial orders from preorders"
    , "Crossproduct lifted poset"
    , "Crossproduct lifted lattice"
    ]
