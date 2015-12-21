module Logic.AbstractLogic.Macro where

import           Types

import           Macro.MetaMacro
import           Macro.Text

import           Functions.Application.Macro

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
linf n m = comm2 "infer" m $ separated ("," <> commS ",") n

-- Logic knowledge base
lkb :: Note
lkb = "KB"

-- Logic sentence
lsen :: Note
lsen = alpha

-- Logical models of
lmo :: Note -> Note
lmo = app "M"

