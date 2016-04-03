module Cryptography.SystemAlgebra.Macro where

import           Types

import qualified Data.Text                   as T
import           Prelude                     (Int, id)

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



-- * Channels

bullet :: Note
bullet = comm0 "bullet"

negSpace :: Int -> Note
negSpace n = commS "kern" <> raw ("-" <> T.pack (show n) <> "px")

comC :: Note
comC = longrightarrow

autC :: Note
autC = bullet <> negSpace 4 <> longrightarrow

secrC :: Note
secrC = longrightarrow <> negSpace 6 <> bullet

secuC :: Note
secuC = bullet <> negSpace 4 <> longrightarrow <> negSpace 6 <> bullet

keyC :: Note
keyC = bullet <> negSpace 5 <> raw "=\\joinrel=\\joinrel=" <> negSpace 6 <> bullet

hkeyC :: Note
hkeyC = raw "=\\joinrel=\\joinrel=" <> negSpace 6 <> bullet


-- | Encryption transformer
encT :: Note -- ^ Encryption function
     -> Note
encT = id

-- | Encryption transformer for @enc_@
encT_ :: Note
encT_ = encT "enc"

-- | Decryption transformer
decT :: Note -- ^ Decryption function
     -> Note
decT = id

-- | Decryption transformer for @dec_@
decT_ :: Note
decT_ = decT "dec"
