module Sets.Basics.Terms where

import           Notes

makeDefs [
      "set"
    , "element"
    , "singleton"
    , "subset"
    , "predicate"
    ]

sets :: Note
sets = index "set" <> "sets"

subsets :: Note
subsets = index "subset" <> "subsets"

makeThm "Every set is a subset of the universe"
makeDe "Set equality"
