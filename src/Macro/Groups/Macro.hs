module Macro.Groups.Macro where

import           Types

import           Macro.MetaMacro
import           Macro.Tuple


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
