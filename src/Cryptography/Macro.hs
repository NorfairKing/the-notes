module Cryptography.Macro where

import           Types

import           Macro.MetaMacro

import           Functions.Application.Macro

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

-- * Xor
xor :: Note -> Note -> Note
xor = binop xor_

(⊕) :: Note -> Note -> Note
(⊕) = xor

xor_ :: Note
xor_ = comm0 "oplus"

xorBig_ :: Note
xorBig_ = comm0 "bigoplus"
