module NumberTheory.Macro where

import           Types

import           Macro.MetaMacro

import           Functions.Application.Macro
import           Macro.Sets.Macro

-- * Natural numbers

succ :: Note -> Note
succ = fn "succ"

nat :: Note -> Note
nat n = n ∈ naturals

nats :: Note
nats = naturals

nats0 :: Note
nats0 = nats !: 0

addN :: Note -> Note -> Note
addN = widebinop addN_

addN_ :: Note
addN_ = add_ `annotateOp` nats

subN :: Note -> Note -> Note
subN = widebinop subN_

subN_ :: Note
subN_ = sub_ `annotateOp` nats

mulN :: Note -> Note -> Note
mulN = widebinop mulN_

mulN_ :: Note
mulN_ = mul_ `annotateOp` nats

divN :: Note -> Note -> Note
divN = widebinop divN_

divN_ :: Note
divN_ = div_ `annotateOp` nats

-- * Operations un numbers
add_ :: Note
add_ = "+"

sub_ :: Note
sub_ = "-"

mul_ :: Note
mul_ = comm0 "cdot"

div_ :: Note
div_ = comm0 "div"


-- * Whole numbers

int :: Note -> Note
int n = n ∈ ints

ints :: Note
ints = integers

intmod :: Note -> Note
intmod n = ints !: n

int0mod :: Note -> Note
int0mod n = ints !: (0 <> "," <> n)

-- | Utils
widebinop :: Note -> Note -> Note -> Note
widebinop n = binop $ raw "\\," <> n <> raw "\\,"

annotateOp :: Note -> Note -> Note
annotateOp = (!:)
