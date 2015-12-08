module Logic.HoareLogic.Macro (
      module Logic.HoareLogic.Macro
    , module Macro.BussProofs
    ) where

import           Types

import           Control.Monad               (sequence_)
import           Prelude                     (map)

import           Macro.Array
import           Macro.BussProofs
import           Macro.Math
import           Macro.MetaMacro


import           Functions.Application.Macro
-- import           Logic.AbstractLogic.Macro
import           Macro.Logic.Macro

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


-- * Proof rules

-- | Rule application
rule :: Note -- ^ Rule name
     -> [Note] -- ^ Hypotheses
     -> Note -- ^ Conclusion
     -> Note
rule name hs c = "" ^: sqbrac name <> linf hs c

-- | Sequential Composition
-- > comp = rule "comp"
seqcomp :: Note -> Note -> Note -> Note
seqcomp = binaryInf "[seqcomp]"

-- | Constancy
-- > constancy = rule "const"
constancy :: Note -> Note -> Note -> Note
constancy = binaryInf "[const]"

-- | Consequence
-- > conseq = rule "consequence"
conseq :: Note -> Note -> Note -> Note -> Note
conseq = trinaryInf "[conseq]"

-- | Consequence with only two arguments
-- This is useful when one of the arguments is @true@ and you would like to keep the tree small
conseq2 :: Note -> Note -> Note -> Note
conseq2 = binaryInf "[conseq]"

-- | Skip axiom schema
-- > skipAs = rule "skip" []
skipAs :: Note -> Note
skipAs = unaryInf "[skip]" axiomC

-- | Assignment axiom schema
-- > assignmentAs = rule "assignment" []
assignmentAs :: Note -> Note
assignmentAs = unaryInf "[ass]" axiomC

-- | Assumption without a label
assumption :: Note -> Note
assumption = unaryInf "" axiomC

elemmath :: Note -> Note
elemmath = unaryInf "[EM]" axiomC
