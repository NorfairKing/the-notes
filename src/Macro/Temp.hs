module Macro.Temp where

import           Types

import           Macro.Index
import           TH

makeIxs
    [ "least significant bit"
    , "base"
    , "infinite"
    , "differentiable"
    , "local minimum"
    , "local maximum"
    , "derivative"
    , "homogenous"
    , "basis"
    , "matrix"
    , "additive"
    , "invertible"
    , "sum"
    , "product"
    , "increasing"
    , "decreasing"
    , "right congruent"
    , "left congruent"
    , "constant"
       -- Matrix pseudo inverse
    , "pseudo inverse"
    , "commutative"
    , "idempotent"
    , "distributive"
    , "sequence"
    , "finite"
      -- Matrix inverse
    , "inverse"
    , "objective function"
    , "gradient"
    , "subgradient"
    , "projection"
    , "closed"
    , "transformation"
    , "directed"
    , "acyclic"
    , "permutation"
    , "countable"
    , "smallest"
      -- Groups
    , "cyclic"
    ]

constants :: Note
constants = ix_ "constant" "constants"

subgradients :: Note
subgradients = ix_ "subgradients" "subgradient"
permutations :: Note
permutations = ix_ "permutations" "permutation"
