module Relations.Orders.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro
import           Macro.Relations.Macro

import           Functions.Application.Macro

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

-- | Minimal element
bot :: Note
bot = comm0 "bot"

-- * Bounds

-- | Least upper bound
(⊔) :: Note -> Note -> Note
(⊔) = binop $ comm0 "sqcup"

inf :: Note -> Note
inf = fn "Inf"

infcomp :: Note -> Note -> Note
infcomp = comp $ commS "bigsqcap"


-- | Greatest lower bound
(⊓) :: Note -> Note -> Note
(⊓) = binop $ comm0 "sqcap"

sup :: Note -> Note
sup = fn "Sup"

supcomp :: Note -> Note -> Note
supcomp = comp $ commS "bigsqcup"

-- * Lattices

latset_ :: Note
latset_ = posetset_

lat :: Note -> Note -> Note
lat = relposet

lat_ :: Note
lat_ = lat latset_ partord_

