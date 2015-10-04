module Logic.Macro where

import           Macro.Math
import           Macro.MetaMacro
import           Macro.Text
import           Types

-- Logic theory
logict :: Note
logict = mathbb "T"

-- Logic formula
logicf :: Note
logicf = "f"

-- Logic inference rule
logicir :: Note
logicir = "i"

-- Logic provable
lpvsign :: Note
lpvsign = comm0 "vdash"

lpv :: Note -> Note -> Note
lpv = between lpvsign

lpvm :: Note -> Note -> Note -> Note
lpvm n = between (commS "vdash" !: n)

-- Logic axiom
la :: Note -> Note
la n = lpvsign <> n

-- Logical entailment
lentsign :: Note
lentsign = comm0 "vDash"

lent :: Note -> Note -> Note
lent = between lentsign

-- Logical inference
linf :: [Note] -> Note -> Note
linf n m = comm2 "infer" m $ commaSeparated n

-- Logic knowledge base
lkb :: Note
lkb = "KB"

-- Logical models of
lmo :: Note -> Note
lmo = funapp "M"

-- Logical negation
neg :: Note -> Note
neg = mnot

-- Logical and
land :: Note -> Note -> Note
land = between $ comm0 "wedge"

(∧) :: Note -> Note -> Note
(∧) = land

-- Logical or
lor :: Note -> Note -> Note
lor = between $ comm0 "vee"

-- Logical or
(∨) :: Note -> Note -> Note
(∨) = lor
