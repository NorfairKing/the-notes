module Functions.Product.Macro where

import           Macro.Lists
import           Macro.Tuple
import           Types

dprodfuns :: [Note] -> Note
dprodfuns = tupleOfs

dprodfunlst :: Note -> Note -> Note
dprodfunlst = tuplelst

dprodfunlist :: Note -> Note -> Note -> Note
dprodfunlist = tuplelist


fprodfuns :: [Note] -> Note
fprodfuns = listofs

fprodfunlst :: Note -> Note -> Note
fprodfunlst = listlst

fprodfunlist :: Note -> Note -> Note -> Note
fprodfunlist = listlist
