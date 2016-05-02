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

-- * Hash function

-- | Concrete hash function
hshf_ :: Note
hshf_ = "h"

-- | Concrete hash function application
hsh :: Note -> Note
hsh = fn hshf_

