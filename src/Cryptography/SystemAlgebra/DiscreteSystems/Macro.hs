module Cryptography.SystemAlgebra.DiscreteSystems.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro
import           Macro.Text

import           Functions.Application.Macro

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

-- | Behaviour of a probabilistic X,Y-system
bhv :: Note -> Note
bhv = fn "b"

-- | System that only considers the first n steps of a system
firstOf :: Note -> Note -> Note
firstOf n sys = sqbrac n <> sys

-- | Behaviour of given in step i probabilistic X,Y-system
bhvs_ :: Note -- ^ The system
     -> Note -- ^ The step i
     -> Note
bhvs_ sys i = "p" .^: sys .!: (yy !: i <> mid <> xx ^ i <> yy ^ (i - 1))
  where
    xx = "X"
    yy = "Y"

bhvs :: Note -- ^ The system
     -> Note -- ^ The step i
     -> Note -- ^ y_i
     -> Note -- ^ x^i
     -> Note -- ^ y^{i-1}
     -> Note
bhvs sys i = fn3 (bhvs_ sys i)

bhvsi_ :: Note -> Note -> Note
bhvsi_ sys i = bhvs sys i (y !: i) (x ^ i) (y ^ (i - 1))
  where
    x = "x"
    y = "y"

-- | Equivalent systems
eqsys :: Note -> Note -> Note
eqsys = binop $ comm0 "equiv"
