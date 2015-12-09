module Logic.HoareLogic.Macro (
      module Logic.HoareLogic.Macro
    , module Macro.BussProofs
    ) where

import           Types

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

-- | Hoare triple in a collumn instead of a row
htrip_ :: Note -> Note -> Note -> Note
htrip_ p a q = leftBelowEachOther [brac p, a, brac q]

-- | Sequence
-- > C-k ;+
(؛) :: Note -> Note -> Note
(؛) = between (";" <> commS " ")

-- | Sequence of instructions below eachother
-- > C-k ;+
seqins :: [Note] -> Note
seqins = leftBelowEachOther

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

-- | If then end
ifThen :: Note -> Note -> Note
ifThen c i = t "if " <> c <> t " then " <> i <> t " end"
  where t = text . textbf

ifThen_ :: Note -> Note -> Note
ifThen_ c i = leftBelowEachOther $
    [
      t "if " <> c
    , t "then"
    , quad <> i
    , t "end"
    ]
  where t = text . textbf

-- | If then else end
ifThenElse :: Note -> Note -> Note -> Note
ifThenElse c i e = t "if " <> c <> t " then " <> i <> t " else " <> e <> t " end"
  where t = text . textbf

-- | If then else end but in a collumn instead of a row
ifThenElse_ :: Note -> Note -> Note -> Note
ifThenElse_ c i e = leftBelowEachOther
    [
      t "if " <> c
    , quad <> i
    , t "else"
    , quad <> e
    , t "end"
    ]
  where t = text . textbf

-- * Loops

-- | from until loop end
fromUntilLoop :: Note -> Note -> Note -> Note
fromUntilLoop a c b = t "from " <> a <> t " until " <> c <> t " loop " <> b <> t " end"
  where t = text . textbf

-- | from until loop end but in a collumn instead of a row
fromUntilLoop_ :: Note -> Note -> Note -> Note
fromUntilLoop_ a c b = leftBelowEachOther
    [
      t "from"
    , quad <> a
    , t "until " <> c <> t " loop"
    , quad <> b
    , t "end"
    ]
  where t = text . textbf

-- * Arrays

-- | Array indexing
-- @index a i@ represents a[i]
index :: Note -> Note -> Note
index a i = a <> sqbrac i

(!) :: Note -> Note -> Note
(!) = index


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
assumption = axiomC_

-- | Elementary Math
elemmath :: Note -> Note
elemmath = unaryInf "[EM]" axiomC

-- | Loop rule
looprule :: Note -> Note -> Note -> Note -> Note
looprule = trinaryInf "[loop]"
