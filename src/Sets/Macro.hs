module Sets.Macro where

import           Macro.Math
import           Macro.MetaMacro
import           Types

setof :: Note -> Note
setof = brac

setcmpr :: Note -> Note -> Note
setcmpr n m = setof $ n <> mid <> m

setlst :: Note -> Note -> Note
setlst n m = setof $ n <> ", " <> dotsc <> ", " <> m

setlist :: Note -> Note -> Note -> Note
setlist m n o = setof $ m <> ", " <> n <> ", " <> dotsc <> ", " <> o

seteqsign :: Note
seteqsign = underset "set" "="

(=§=) :: Note -> Note -> Note
(=§=) = binop seteqsign

setneqsign :: Note
setneqsign = underset "set" $ comm0 "neq"

-- C-k (-
(∈) :: Note -> Note -> Note
(∈) = in_

-- C-k (_
(⊆) :: Note -> Note -> Note
(⊆) = subseteq

subsetneqsign :: Note
subsetneqsign = comm0 "subsetneq"

subsetneq :: Note -> Note -> Note
subsetneq = binop subsetneqsign

setneq :: Note -> Note -> Note
setneq = binop setneqsign

setuniverse :: Note
setuniverse = comm0 "Omega"

emptyset :: Note
emptyset = comm0 "emptyset"

setunsign :: Note
setunsign = comm0 "cup"

setun :: Note -> Note -> Note
setun = binop setunsign
