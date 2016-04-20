module Cryptography.Macro where

import           Types

import           Functions.Application.Macro

-- | Least significant bit
lsb :: Note -> Note
lsb = fn "LSB"

-- * Hash function

-- | Concrete hash function
hshf_ :: Note
hshf_ = "h"

-- | Concrete hash function application
hsh :: Note -> Note
hsh = fn hshf_

