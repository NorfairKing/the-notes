module Relations.Orders.Macro where

import           Types

import           Macro.MetaMacro
import           Macro.Tuple

import           Functions.Application.Macro
import           Relations.Preorders.Macro

-- * Partial order
partord_ :: Note
partord_ = preord_

ipartord_ :: Note
ipartord_ = ipreord_

-- * Poset
posetset_ :: Note
posetset_ = "X"

relposet :: Note -> Note -> Note
relposet = tuple

relposet_ :: Note
relposet_ = relposet posetset_ partord_

inposet :: Note -> Note -> Note -> Note
inposet = inpreord

inposet_ :: Note -> Note -> Note
inposet_ = binop partord_

iinposet_ :: Note -> Note -> Note
iinposet_ = binop ipartord_

-- |
-- > C-k (_
(⊆:) :: Note -> Note -> Note
(⊆:) = inposet_

-- |
-- > C-k )_
(⊇:) :: Note -> Note -> Note
(⊇:) = iinposet_

-- * Total order
totord :: Note
totord = comm0 "le"

-- * Extreme elements

-- | Maximal element
top :: Note
top = comm0 "top"

-- | Minimal element (bot) in HaTeX

-- * Bounds

-- ** Least upper bound

supsign :: Note
supsign = comm0 "sqcup"

(⊔) :: Note -> Note -> Note
(⊔) = binop supsign

sup :: Note -> Note
sup = fn "Sup"

bigsupsign :: Note
bigsupsign = commS "bigsqcup"

supcomp :: Note -> Note -> Note
supcomp = comp bigsupsign

supof :: Note -> Note
supof = (supsign <>)

-- | Supremum, modified
supofm :: Note -> Note -> Note
supofm n = (supsign !: n <>)

-- ** Greatest lower bound

infsign :: Note
infsign = comm0 "sqcap"

(⊓) :: Note -> Note -> Note
(⊓) = binop infsign

inf :: Note -> Note
inf = fn "Inf"

biginfsign :: Note
biginfsign = commS "bigsqcap"

infcomp :: Note -> Note -> Note
infcomp = comp biginfsign

infof :: Note -> Note
infof = (infsign <>)

-- | Infimum, modified
infofm :: Note -> Note -> Note
infofm n = (infsign !: n <>)

-- * Lattices

latset_ :: Note
latset_ = posetset_

lat :: Note -> Note -> Note
lat = relposet

lat_ :: Note
lat_ = lat latset_ partord_

