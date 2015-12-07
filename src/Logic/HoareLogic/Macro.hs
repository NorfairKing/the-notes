module Logic.HoareLogic.Macro where

import           Types

import           Control.Monad               (sequence_)
import           Prelude                     (map)

import           Macro.Array
import           Macro.Math


import           Functions.Application.Macro

-- | Hoare Triple
htrip :: Note -> Note -> Note -> Note
htrip p a q = brac p <> commS "," <> a <> commS "," <> brac q

-- | Sequence
-- > C-k ;+
(؛) :: Note -> Note -> Note
(؛) = between (";" <> commS " ")

-- | Sequence of instructions below eachother
-- > C-k ;+
seqins :: [Note] -> Note
seqins = array Nothing [CenterColumn] . sequence_ . map (\n -> n <> ";" <> lnbk)

-- * Replacement
lrepl :: Note -> Note -> Note -> Note
lrepl p e x = p <> sqbrac (e <> " / " <> x)

-- *  Assignment
lass :: Note -> Note -> Note
lass = between ":="

(=:=) :: Note -> Note -> Note
(=:=) = lass


freevars :: Note ->  Note
freevars = app "FV"

modifies :: Note -> Note
modifies = app "modifies"

-- * Conditionals

-- | If then else end
ifThenElse :: Note -> Note -> Note -> Note
ifThenElse c i e = text "if " <> c <> text " then " <> i <> text " else " <> e <> text " end"

-- * Loops

-- | from until loop end
fromUntilLoop :: Note -> Note -> Note -> Note
fromUntilLoop a c b = text "from " <> a <> text " until " <> c <> text " loop " <> b <> text " end"

