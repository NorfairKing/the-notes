module Groups.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro
import           Macro.Tuple

-- * Magma

-- | Magma
mgm :: Note -> Note -> Note
mgm = tuple

-- | Magma Set
mgms_ :: Note
mgms_ = "M"

-- | Concrete Magma operation
mgmop_ :: Note -> Note -> Note
mgmop_ = binop $ comm2 "raisebox" "-0.25ex" $ comm2 "scalebox" "1.2" $ m $ cdot_

-- | Infix version of the above
-- > C-k .M
(·) :: Note -> Note -> Note
(·) = mgmop_

-- | Concrete Magma
mgm_ :: Note
mgm_ = mgm mgms_ $ "" · ""


-- * Semigroups
sgrp :: Note -> Note -> Note
sgrp = tuple

-- | Semigroup set
sgrps_ :: Note
sgrps_ = "S"

-- | Semigroup operation
sgrpop_ :: Note -> Note -> Note
sgrpop_ = mgmop_

-- | Infix version of the above
-- > C-k '.
(˙) :: Note -> Note -> Note
(˙) = sgrpop_

sgrp_ :: Note
sgrp_ = sgrp sgrps_ $ "" ˙ ""

-- * Monoids

-- | Monoid
mnd :: Note -> Note -> Note
mnd = tuple

-- | Concrete monoid set
mnds_ :: Note
mnds_ = "M"

-- | Concrete monoid operation
mndop_ :: Note -> Note -> Note
mndop_ = sgrpop_

-- | Infix version of the above
-- > C-k '0
(˚) :: Note -> Note -> Note
(˚) = mndop_

-- | Concrete Monoid
mnd_ :: Note
mnd_ = mnd mnds_ $ "" ˚ ""

-- | Monoid identity
mid_ :: Note
mid_ = "e"

