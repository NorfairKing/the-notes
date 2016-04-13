module Cryptography.SymmetricCryptography.Macro where

import           Types

import           Macro.MetaMacro
import           Macro.Tuple

import           Functions.Application.Macro
import           Macro.Sets.Macro

-- * Concatenation of messages
(++) :: Note -> Note -> Note
(++) = binop $ commS " " <> "|" <> commS " "

-- conccmp :: Note -> Note -> Note
-- conccmp =

-- | Encryption function
enc_ :: Note
enc_ = "e"

enc :: Note -> Note -> Note -> Note
enc = fn3 enc_

enc' :: Note -> Note -> Note
enc' m k = enc m k $ comm1 "text" "_"

-- | Decryption function
dec_ :: Note
dec_ = "d"

dec :: Note -> Note -> Note
dec = fn2 dec_

-- | Symmetric cryptosystem
scs :: Note -> Note -> Note
scs = tuple

-- | Concrete Symmetric cryptosystem
scs_ :: Note
scs_ = scs enc_ dec_

-- | Message space
msp_ :: Note
msp_ = mathcal "M"

-- | Ciphertext space
csp_ :: Note
csp_ = mathcal "C"

-- | Key space
ksp_ :: Note
ksp_ = mathcal "K"

-- | Randomness space
rsp_ :: Note
rsp_ = mathcal "R"

-- * Pseudorandom generator

gen_ :: Note
gen_ = "g"

gen :: Note -> Note
gen = fn gen_

-- * Bitfield

-- | bit set
bits :: Note
bits = setofs [0, 1]

-- | bits set
bitss :: Note -> Note
bitss n = bits ^: n

-- * Ternary field
terns :: Note
terns = setofs [0, 1, 2]

ternss :: Note -> Note
ternss n = terns ^: n

-- | Length of a bitstring
len :: Note -> Note
len = autoBrackets "|" "|"
