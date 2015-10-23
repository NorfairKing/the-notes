module Macro.Groups.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro


grpset :: Note
grpset = "G"

grpadd :: Note
grpadd = "*"

(.+.) :: Note -> Note -> Note
(.+.) = binop grpadd

grp :: Note
grp = grp_ grpset grpadd

grp_ :: Note -- Set
     -> Note -- Additive Operation
     -> Note
grp_ = tuple
