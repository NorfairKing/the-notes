module Relations.Domain.Macro where

import           Types

import           Functions.Application.Macro (fn)

-- * Domain

-- | Standand domain sign
domsign :: Note
domsign = "Dom"

-- | Domain of a given relation
dom :: Note -> Note
dom = fn domsign

-- * Image

-- | Standard image sign
imgsign :: Note
imgsign = "Img"

-- | Image of a given relation
img :: Note -> Note
img = fn imgsign

