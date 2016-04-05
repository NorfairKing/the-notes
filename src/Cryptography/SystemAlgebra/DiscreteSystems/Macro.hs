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

-- | Behaviour of a probabillistic X,Y-system
bhv :: Note -> Note
bhv = fn "b"


