module Logic.PropositionalLogic.Macro where

import           Macro.Arrows

import           Notes

-- Truth values
true :: Note
true = "true"

false :: Note
false = "false"

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


-- If and only if
iffsign :: Note
iffsign = leftRightarrow

iff :: Note -> Note -> Note
iff m n = m <> iffsign <> n

-- C-k ==
(⇔) :: Note -> Note -> Note
(⇔) = iff

impliessign :: Note
impliessign = rightArrow

mimplies :: Note -> Note -> Note
mimplies m n = m <> impliessign <> n


-- C-k =>
(⇒) :: Note -> Note -> Note
(⇒) = mimplies


