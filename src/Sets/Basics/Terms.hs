module Sets.Basics.Terms where

import           Notes

makeDefs [
      "set"
    , "element"
    , "singleton"
    , "subset"
    , "predicate"
    ]

makeThm "Every set is a subset of the universe"
makeDe "Set equality"


asetof :: Note
asetof = "a " <> set <> " of"
