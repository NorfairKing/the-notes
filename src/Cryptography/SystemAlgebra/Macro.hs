module Cryptography.SystemAlgebra.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro

import           Functions.Application.Macro

-- | Concrete set of systems
syss_ :: Note
syss_ = phiu

-- | Concrete set of labels
labs_ :: Note
labs_ = lambdau

-- | Concrete Label assignment function
laf_ :: Note
laf_ = lambda

-- | Application of concrete Label assignment function
la :: Note -> Note
la = fn laf_


-- | Concrete system merging operation
smo_ :: Note
smo_ = comm0 "bigvee"

-- | System merging operation
sm :: Note -> Note -> Note
sm = binop smo_

-- | Interface connection operation
ico :: Note -- ^ System
    -> Note -- ^ Interface 1
    -> Note -- ^ Interface 2
    -> Note
ico s i1 i2 = s ^ (i1 <> "-" <> i2)

-- | System with empty interface label set
emptysys :: Note
emptysys = comm0 "blacksquare"
