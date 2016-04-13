module Functions.Order.Terms where

import           Notes

makeDefs [
      "monotonic"
    , "monotone"
    , "isotone"
    , "order preserving"
    , "Scott continuous"
    , "fixed point"
    , "fixed point region"
    , "ascending region"
    , "pre-fixedpoint"
    , "descending region"
    , "post-fixedpoint"
    , "least fixed point"
    , "greatest fixed point"
    , "Kleene chain"
    , "function iterates"

    , "completely meet-preserving"
    , "completely join-preserving"

    , "Galois connection"
    , "reductive"
    , "extensive"
    , "Galois insertion"

    , "approximates"
    , "approximation"
    , "least precise approximation"
    , "most precise approximation"
    ]

makeThms [
      "Monotonic functions closed under composition"
    , "Scott continuous implies monotonic"
    , "Descending region is closed under application"
    , "Ascending region is closed under application"
    , "Top element is in descending region"
    , "Bottom element is in ascending region"
    , "Fixed point region is intersection of ascending region and descending region"
    , "Lattices over functions"
    ]

