module Sets.Macro where

import           Macro.Index
import           Macro.Math
import           Macro.MetaMacro
import           Types

--[ Set of
setof :: Note -> Note
setof = brac


--[ Set comprehension
setcmpr :: Note -> Note -> Note
setcmpr n m = setof $ n <> mid <> m


--[ Set list
setlst :: Note -> Note -> Note
setlst n m = setof $ n <> ", " <> dotsc <> ", " <> m

setlist :: Note -> Note -> Note -> Note
setlist m n o = setof $ m <> ", " <> n <> ", " <> dotsc <> ", " <> o


--[ Set equals
seteqsign :: Note
seteqsign = underset "set" "="

seteq :: Note -> Note -> Note
seteq = binop seteqsign

(=§=) :: Note -> Note -> Note
(=§=) = seteq


--[ Set not equals
setneqsign :: Note
setneqsign = underset "set" $ comm0 "neq"

setneq :: Note -> Note -> Note
setneq = binop setneqsign

--[ Element of
-- C-k (-
(∈) :: Note -> Note -> Note
(∈) = in_


--[ Not element of
nin :: Note -> Note -> Note
nin = binop $ comm1 "not" $ comm0 "in"


--[ Subseteq
-- C-k (_
(⊆) :: Note -> Note -> Note
(⊆) = subseteq


--[ Subsetneq
subsetneqsign :: Note
subsetneqsign = comm0 "subsetneq"

subsetneq :: Note -> Note -> Note
subsetneq = binop subsetneqsign


--[ Universal set
setuniv :: Note
setuniv = comm0 "Omega"


--[ Empty set
emptyset :: Note
emptyset = comm0 "emptyset"


--[ Set union
setunsign :: Note
setunsign = comm0 "cup"

setun :: Note -> Note -> Note
setun = binop setunsign

-- C-k )U
(∪) :: Note -> Note -> Note
(∪) = setun


--[ set union comprehension
setuncmprsign :: Note
setuncmprsign = commS "bigcup"

setuncmpr :: Note -> Note -> Note -> Note
setuncmpr = compr setuncmprsign

setuncmp :: Note -> Note -> Note
setuncmp = comp setuncmprsign


--[ Set intersection
setinsign :: Note
setinsign = comm0 "cap"

setin :: Note -> Note -> Note
setin = binop setinsign

-- C-k (U
(∩) :: Note -> Note -> Note
(∩) = setin


--[ set intersectino comprehension
setincmprsign :: Note
setincmprsign = commS "bigcap"

setincmpr :: Note -> Note -> Note -> Note
setincmpr = compr setincmprsign

setincmp :: Note -> Note -> Note
setincmp = comp setincmprsign


--[ Set complement
setc :: Note -> Note
setc n = braces n ^: "C"

-- Relative set complement
setrelc :: Note -> Note -> Note
setrelc n m = setc n !: m


--[ Set difference
setdiffsign :: Note
setdiffsign = comm0 "setminus"

setdiff :: Note -> Note -> Note
setdiff = binop setdiffsign

(\\) :: Note -> Note -> Note
(\\) = setdiff


--[ Symmetric set difference
setsdiffsign :: Note
setsdiffsign = comm0 "Delta"

setsdiff :: Note -> Note -> Note
setsdiff = binop setsdiffsign


--[ Set product
setprodsign :: Note
setprodsign = comm0 "times"

setprod :: Note -> Note -> Note
setprod = binop setprodsign


--[ Powerset
powsetsign :: Note
powsetsign = mathcal "P"

powset :: Note -> Note
powset set = powsetsign `funapp` pars set


--[ Set size
setsize :: Note -> Note
setsize = autoBrackets "|" "|"



--[ Text

set :: Note
set = ix "set"

