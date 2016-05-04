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

-- * Operations un numbers
addition :: Note
addition = "+"

multiplication :: Note
multiplication = comm0 "cdot"


-- * Whole numbers

int :: Note -> Note
int n = n ∈ integers

intmod :: Note -> Note
intmod n = integers !: n

int0mod :: Note -> Note
int0mod n = integers !: (0 <> "," <> n)
