module Cryptography.Macro where

import           Types

import           Functions.Application.Macro



-- | Encryption function
enc_ :: Note
enc_ = "e"

enc :: Note -> Note -> Note -> Note
enc = fn3 enc_

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
