module NumberTheory.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro
import           Macro.Tuple

import           Functions.Application.Macro
import           Groups.Macro
import           Macro.Sets.Macro

-- * Natural numbers

succ :: Note -> Note
succ = fn "succ"

nat :: Note -> Note
nat n = n ∈ naturals

nats :: Note
nats = mathbb "N"

nats0 :: Note
nats0 = nats !: 0

addN :: Note -> Note -> Note
addN = binop addN_

addN_ :: Note
addN_ = add_ `annotateOp` nats

subN :: Note -> Note -> Note
subN = binop subN_

subN_ :: Note
subN_ = sub_ `annotateOp` nats

mulN :: Note -> Note -> Note
mulN = binop mulN_

mulN_ :: Note
mulN_ = mul_ `annotateOp` nats

divN :: Note -> Note -> Note
divN = binop divN_

divN_ :: Note
divN_ = div_ `annotateOp` nats

-- * Whole numbers

int :: Note -> Note
int n = n ∈ ints

ints :: Note
ints = mathbb "Z"

wholen :: Note -> Note -> Note
wholen = tuple

addZ :: Note -> Note -> Note
addZ = binop addZ_

addZ_ :: Note
addZ_ = add_ `annotateOp` ints

subZ :: Note -> Note -> Note
subZ = binop subZ_

subZ_ :: Note
subZ_ = sub_ `annotateOp` ints

mulZ :: Note -> Note -> Note
mulZ = binop mulZ_

mulZ_ :: Note
mulZ_ = mul_ `annotateOp` ints

divZ :: Note -> Note -> Note
divZ = binop divZ_

divZ_ :: Note
divZ_ = div_ `annotateOp` ints

-- * Modular ints

-- | Congruence modulo an integer
eqmod :: Note -> Note -> Note -> Note
eqmod n a b = (binop (comm0 "equiv") a b) <> raw "\\;" <> pars (text "mod " <> n)

intmod :: Note -> Note
intmod n = ints !: n

int0mod :: Note -> Note
int0mod n = ints !: (0 <> "," <> n)

-- | Additive group of ints modulo n
intagrp :: Note -> Note
intagrp n = grp (intmod n) $ "" + ""

-- | Multiplicative group of ints modulo n
intmgrp :: Note -> Note
intmgrp n = grp (int0mod n) cdot_

-- | Divides
(.|) :: Note -> Note -> Note
(.|) = binop $ comm0 "mid"

-- | Greatest common divisor
gcd :: Note -> Note -> Note
gcd = fn2 $ comm0 "gcd"

-- | Least common multiple
lcm :: Note -> Note -> Note
lcm = fn2 "lcm"

-- | Coprime
copr :: Note -> Note -> Note
copr = binop $ comm0 "bot"

-- * Operations on numbers
add_ :: Note
add_ = "+"

sub_ :: Note
sub_ = "-"

mul_ :: Note
mul_ = comm0 "cdot"

div_ :: Note
div_ = comm0 "div"


-- | Utils
annotateOp :: Note -> Note -> Note
annotateOp op ann = raw "\\," <> op !: ann <> raw "\\;"
