module Rings.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro
import           Macro.Tuple

import           NumberTheory.Macro

-- * Rings

-- | Ring
rng :: Note -- ^ Set
    -> Note -- ^ Additive operation
    -> Note -- ^ Multiplicative operation
    -> Note
rng = triple

-- | Concrete ring set
rngs_ :: Note
rngs_ = "R"

-- | Concrete ring additive operation
rngaop_ :: Note
rngaop_ = "+"

-- | Infix version of the above
(.+) :: Note -> Note -> Note
(.+) = binop rngaop_

-- | Concrete ring multiplicative operation
rngmop_ :: Note
rngmop_ = "*"

-- | Infix version of the above
(.*) :: Note -> Note -> Note
(.*) = binop rngmop_

-- | Concrete ring
rng_ :: Note
rng_ = rng rngs_ rngaop_ rngmop_

-- | Ring Neutral
rnt_ :: Note
rnt_ = "e"

-- | Ring Identity
rid_ :: Note
rid_ = "i"

-- | Inverse element (for the multiplicative operation) in a ring
rinv :: Note -> Note
rinv = (^ "-1")

-- | Inverse element (for the additive operation) in a ring
rmin :: Note -> Note
rmin = ("-" <>)

-- | Inverse element in a given ring
rinvm :: Note -> Note -> Note
rinvm r n = "" !: r <> n ^ "-1"

-- | Integer ring modulo n
intring :: Note -> Note
intring n = rng (intmod n) ("" + "") cdot_
