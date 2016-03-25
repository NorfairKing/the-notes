module Groups.Terms where

import           Notes hiding (cyclic, inverse)

makeDefs
    [ "magma"
    , "semigroup"
    , "monoid"
    , "group"
    , "subgroup"
    , "trivial subgroup"
    , "inverse"
    , "cyclic"
    , "generator"
    , "order"
    ]


makeThms
    [ "inverse unique"
    , "inverse of applied operation"
    , "subgroup same identity"
    , "generated set is group"
    , "trivial subgroups"
    , "element order divides group order"
    ]
