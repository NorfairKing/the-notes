module Cryptography.SystemAlgebra.Terms where

import           Notes

makeDefs
    [ "abstract system algebra"
    , "system algebra"
    , "system"
    , "label"
    , "interface label set"
    , "interface"
    , "system merging operation"
    , "interface connection operation"
    , "interface merging"
    , "composition"
    , "parallel composition"
    , "resource system"
    , "resource"
    , "converter system"
    , "converter"
    , "source"
    , "beacon"
    , "uniform random function"
    , "URF"
    ]

nS :: Note -> Note
nS n = m n <> "-" <> system

nSs :: Note -> Note
nSs n = m n <> "-" <> systems

xyS :: Note -> Note -> Note
xyS x y = m (tuple x y) <> "-" <> system

yS :: Note -> Note
yS y = m y <> "-" <> source
