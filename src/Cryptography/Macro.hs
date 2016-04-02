module Cryptography.Macro where

import           Types

import           Functions.Application.Macro

-- * Hash function

-- | Concrete hash function
hshf_ :: Note
hshf_ = "h"

-- | Concrete hash function application
hsh :: Note -> Note
hsh = fn hshf_

