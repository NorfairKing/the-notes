module Functions.BinaryOperation.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro              (binop)

import           Functions.Basics.Macro
import           Macro.Sets.CarthesianProduct

-- * Binary operations

-- | Standard binary operation sign
binop_ :: Note
binop_ = comm0 "star"

-- | Binary operation function definition
binopdef :: Note -- ^ Sign
         -> Note -- ^ Corange
         -> Note
binopdef f a = fun (pars f) (a ⨯ a) a

-- | Standard binary operation function definition
binopdef_ :: Note
binopdef_ = binopdef binop_ dom_

-- | Application of given binary operation
binopapp :: Note -- ^ Sign
         -> Note -> Note -> Note
binopapp = binop

-- | Application of standard binary operation
-- > binopapp_ = binop binop_
binopapp_ :: Note -> Note -> Note
binopapp_ = binop binop_

-- C-k 2*
(★) :: Note -> Note -> Note
(★) = binopapp_

-- | Binary Identity
bid_ :: Note
bid_ = "i"
