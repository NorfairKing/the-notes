module Groups.Terms where

import           Notes hiding (cyclic, inverse)

makeDefs
    [ "magma"
    , "semigroup"
    , "monoid"
    , "group"
    , "neutral element"
    , "subgroup"
    , "trivial subgroup"
    , "inverse"
    , "cyclic"
    , "generator"
    , "order"

    , "square"
    , "square root"

    , "quotient group"
    ]


makeThms
    [ "inverse unique"
    , "inverse of applied operation"
    , "subgroup same identity"
    , "generated set is group"
    , "trivial subgroups"
    , "element order divides group order"
    , "square root unique in finite odd group"
    , "finite odd group root computation"
    ]
