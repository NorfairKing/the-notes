module Logic.PropositionalLogic.Macro where

import           Macro.Arrows
import           Macro.MetaMacro

import           Notes

-- * Truth values
true :: Note
true = "true"

false :: Note
false = "false"

-- * Logical negation
neg :: Note -> Note
neg = not

-- * Logical and
landsign :: Note
landsign = comm0 "wedge"

land :: Note -> Note -> Note
land = between landsign

-- | C-k AN
(∧) :: Note -> Note -> Note
(∧) = land

andcomp :: Note -> Note -> Note
andcomp = comp $ comm0 "bigwedge"

andcompr :: Note -> Note -> Note -> Note
andcompr = compr $ comm0 "bigwedge"


-- * Logical or
lorsign :: Note
lorsign = comm0 "vee"

lor :: Note -> Note -> Note
lor = between lorsign

-- | C-k OR
(∨) :: Note -> Note -> Note
(∨) = lor

orcomp :: Note -> Note -> Note
orcomp = comp $ comm0 "bigvee"

orcompr :: Note -> Note -> Note -> Note
orcompr = compr $ comm0 "bigvee"

-- * Logical Xor
xor_ :: Note
xor_ = comm0 "oplus"

xor :: Note -> Note -> Note
xor = binop xor_

(⊕) :: Note -> Note -> Note
(⊕) = xor

xorBig_ :: Note
xorBig_ = comm0 "bigoplus"

-- * If and only if
iffsign :: Note
iffsign = leftRightarrow

iff :: Note -> Note -> Note
iff m n = m <> iffsign <> n

-- C-k ==
(⇔) :: Note -> Note -> Note
(⇔) = iff

-- * Implies

impliessign :: Note
impliessign = rightArrow

mimplies :: Note -> Note -> Note
mimplies m n = m <> impliessign <> n

-- C-k =>
(⇒) :: Note -> Note -> Note
(⇒) = mimplies


