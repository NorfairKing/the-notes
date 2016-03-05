module Functions.Order.Terms where

import           Notes

makeDefs [
      "monotonic"
    , "monotone"
    , "Scott continuous"
    , "fixed point"
    , "fixed point region"
    , "ascending region"
    , "descending region"
    , "least fixed point"
    , "greatest fixed point"
    , "Kleene chain"
    ]

makeThms [
      "Monotonic functions closed under composition"
    , "Descending region is closed under application"
    , "Ascending region is closed under application"
    , "Top element is in descending region"
    , "Bottom element is in ascending region"
    , "Fixed point region is intersection of ascending region and descending region"
    , "Lattices over functions"
    ]

