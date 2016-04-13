module Sets.Multiset.Macro where

import           Types

import           Macro.MetaMacro
import           Macro.Sets.Macro

-- | Multiset union
msetun :: Note -> Note -> Note
msetun = binop $ setunsign ^: comm0 "sharp"

-- | Multiset difference
msetdiff :: Note -> Note -> Note
msetdiff = binop $ setdiffsign ^: comm0 "sharp"
