module Sets.Macro.CarthesianProduct where

import           Types

import           Macro.MetaMacro

--[ Set product
setprodsign :: Note
setprodsign = comm0 "times"

setprod :: Note -> Note -> Note
setprod = binop setprodsign

-- C-k cp (custom)
(⨯) :: Note -> Note -> Note
(⨯) = setprod

