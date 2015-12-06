module Functions.Order.Macro where

import           Macro.Functions.Application (fn)
import           Types

-- * Regions

-- | Fixed point region
fix :: Note -> Note
fix = fn "Fix"

-- | Ascending region
asc :: Note -> Note
asc = fn "Asc"

-- | Descending region
desc :: Note -> Note
desc = fn "Desc"

-- * Extreme fixed points

-- | Least fixed point
lfp :: Note -> Note
lfp = fn "lfp"

-- | Greatest fixed point
gfp :: Note -> Note
gfp = fn "gfp"

-- * Kleene

-- | Kleene chain
kleeneCh :: Note -> Note
kleeneCh = fn "K"


