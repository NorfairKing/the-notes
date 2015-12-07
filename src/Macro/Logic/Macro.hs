module Macro.Logic.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro
import           Macro.Text

import           Functions.Application.Macro

-- Truth values
true :: Note
true = "true"

false :: Note
false = "false"

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

-- Logical negation
neg :: Note -> Note
neg = not

-- Logical and
landsign :: Note
landsign = comm0 "wedge"

land :: Note -> Note -> Note
land = between landsign

-- C-k AN
(∧) :: Note -> Note -> Note
(∧) = land

-- Logical or
lorsign :: Note
lorsign = comm0 "vee"

lor :: Note -> Note -> Note
lor = between lorsign

-- C-k OR
(∨) :: Note -> Note -> Note
(∨) = lor

-- Logical Xor
xor :: Note -> Note -> Note
xor = between $ comm0 "oplus"


-- Quantifiers
existentialQuantifier :: Note
existentialQuantifier = comm0 "exists"

thereExistsSign :: Note
thereExistsSign = existentialQuantifier

te :: Note -> Note -> Note
te n m = thereExistsSign <> n <> ":" <> commS " " <> m

universalQuantifier :: Note
universalQuantifier = comm0 "forall"

forallSign :: Note
forallSign = universalQuantifier

fa :: Note -> Note -> Note
fa n m = forallSign <> n <> ":" <> commS " " <> m

