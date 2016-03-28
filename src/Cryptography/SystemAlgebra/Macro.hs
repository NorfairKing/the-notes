module Cryptography.SystemAlgebra.Macro where

import           Types

import           Macro.Arrows
import           Macro.Math
import           Macro.MetaMacro
import           Macro.Text

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

-- | Merging interfaces
mio :: Note -- ^ System
    -> Note -- ^ Interface set
    -> Note -- ^ Resulting interface
    -> Note
mio s l j = s ^ (l <> rightarrow <> j)


-- | Merging interfaces inverse operation
mioi :: Note -- ^ System
     -> Note -- ^ Interface set
     -> Note -- ^ Resulting interface
     -> Note
mioi s j l = s ^ (sqbrac $ j <> rightarrow <> l)


-- | Convert resource with converter
conv :: Note -- ^ Converter
     -> Note -- ^ Converted interface
     -> Note -- ^ Resource
     -> Note
conv a i s = a ^ i <> s

-- | Convert 1-resource with converter
conv_ :: Note -- ^ Converter
      -> Note -- ^ Resource
      -> Note
conv_ = (<>)


-- | Bitstring beacon
bitsbea :: Note -> Note
bitsbea n = textbf "B" !: n

-- | Uniform bitstring beacon
ubitsbea :: Note -> Note
ubitsbea n = textbf "U" !: n

-- | Uniform random function
urf :: Note -> Note -> Note
urf m n = textbf "R" !: cs [m, n]


-- | Synchronous composition
syncomp :: Note -> Note -> Note
syncomp = binop "|"

-- | Asynchronous composition
asyncomp :: Note -> Note -> Note
asyncomp a b = sqbrac $ cs [a, b]

-- | Transcript of system and environment
transcr :: Note -> Note -> Note
transcr = fn2 "tr"

-- | Behaviour of a probabillistic X,Y-system
bhv :: Note -> Note
bhv = fn "b"






