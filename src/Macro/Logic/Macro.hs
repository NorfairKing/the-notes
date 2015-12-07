module Macro.Logic.Macro where

import           Types

-- import           Macro.Functions.Macro

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
linf n m = comm2 "infer" m $ separated ("," <> quad) n

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



-- Hoare Triple
htrip :: Note -> Note -> Note -> Note
htrip p a q = brac p <> commS "," <> a <> commS "," <> brac q

-- Sequence C-k ;+
(؛) :: Note -> Note -> Note
(؛) = between (";" <> commS " ")

-- Logic Replacement
lrepl :: Note -> Note -> Note -> Note
lrepl p e x = p <> sqbrac (e <> " / " <> x)

-- Logic Assignment
lass :: Note -> Note -> Note
lass = between ":="

(=:=) :: Note -> Note -> Note
(=:=) = lass

freevars :: Note ->  Note
freevars = app "FV"

modifies :: Note -> Note
modifies = app "modifies"

-- If then else
ifThenElse :: Note -> Note -> Note -> Note
ifThenElse c i e = text "if " <> c <> text " then " <> i <> text " else " <> e <> text " end"

fromUntilLoop :: Note -> Note -> Note -> Note
fromUntilLoop a c b = text "from " <> a <> text " until " <> c <> text " loop " <> b <> text " end"


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

