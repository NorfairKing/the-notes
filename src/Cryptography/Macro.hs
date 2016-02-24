module Cryptography.Macro where

import           Types




-- | Encryption function
enc_ :: Note
enc_ = "e"

-- | Decryption function
dec_ :: Note
dec_ = "d"

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
