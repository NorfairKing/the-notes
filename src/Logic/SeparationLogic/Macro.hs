module Logic.SeparationLogic.Macro (
      module Logic.SeparationLogic.Macro
    , module Macro.BussProofs
    ) where

import           Functions.Application.Macro
import qualified Logic.HoareLogic.Macro      as HL
import           Macro.BussProofs
import           Macro.Math
import           Macro.MetaMacro
import           Macro.Text                  (cs)
import           Types

-- | Empty heap
emp :: Note
emp = "emp"

-- * Separating conjunction

-- | Separating conjunction
sepconj :: Note -> Note -> Note
sepconj = binop "*"

-- | Infix operator for separating conjunction
(.*) :: Note -> Note -> Note
(.*) = sepconj

-- * Separating implication

-- | Separating implication
sepimp :: Note -> Note -> Note
sepimp = binop $ rightarrow <> negspace <> "*"
  where negspace = commS "kern" <> raw "-8pt"

-- | Infix operator for separating implication
(-*) :: Note -> Note -> Note
(-*) = sepimp

-- * Satisfaction
satis :: Note -- ^ Program state
      -> Note -- ^ Heap
      -> Note -- ^ Assertion
      -> Note
satis s h = HL.satis (cs [s, h])

-- * Pointer resulotion

-- | The location of a variable's value
resolve :: Note -- ^ Heap
        -> Note -- ^ Variable
        -> Note
resolve heap variable = sqbrac variable !: heap

-- | Infix operator for @resolve@
(.&) :: Note -- ^ Variable
     -> Note -- ^ Heap
     -> Note
(.&) var heap = resolve heap var

-- * Heap allocation

-- | Allocate space for, and store, a sequence of values
cons :: [Note] -> Note
cons = fn "cons" . cs

-- * Pointer disposal

-- | Dispose of a variable
dispose :: Note -> Note
dispose = fn "dispose"

-- * Frame rule
framerule :: Note -> Note -> Note
framerule = unaryInf "[frame]"
