module Cryptography.Macro where

import           Types

import           Functions.Application.Macro

-- | Least significant bit
lsb :: Note -> Note
lsb = fn "LSB"

-- * Digital signatures

-- | Signature space
ssp_ :: Note
ssp_ = mathcal "S"

-- | Signing key spacke
sigsp_ :: Note
sigsp_ = mathcal "Z"

-- | Verification key spacke
versp_ :: Note
versp_ = mathcal "V"

-- | Signing algorithm
signf_ :: Note
signf_ = sigma

-- | The signature of a message given a signing key
sign :: Note -> Note -> Note
sign = fn2 signf_

-- | Verification algorithm
verif_ :: Note
verif_ = tau

-- | The verification of a message given a signature and a verification key
veri :: Note -> Note -> Note -> Note
veri = fn3 verif_

-- * Hash function

-- | Concrete hash function
hshf_ :: Note
hshf_ = "h"

-- | Concrete hash function application
hsh :: Note -> Note
hsh = fn hshf_

