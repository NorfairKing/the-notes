module Cryptography.Macro where

import           Types

import           Functions.Application.Macro

-- * Public-key encryption

sksp_ :: Note
sksp_ = "s" <> mathcal "K"

pksp_ :: Note
pksp_ = "p" <> mathcal "K"

aenc_ :: Note
aenc_ = "aenk"

aenc :: Note -> Note -> Note -> Note
aenc = fn3 aenc_

adec_ :: Note
adec_ = "adec"

adec :: Note -> Note -> Note
adec = fn2 adec_



-- * Hash function

-- | Concrete hash function
hshf_ :: Note
hshf_ = "h"

-- | Concrete hash function application
hsh :: Note -> Note
hsh = fn hshf_

