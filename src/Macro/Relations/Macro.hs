module Macro.Relations.Macro where

import           Macro.Math
import           Macro.MetaMacro

import           Functions.Application.Macro (fn)

import           Types

-- Basic Relation
rel :: Note
rel = "R"

inrel_ :: Note -> Note -> Note -> Note
inrel_ r v w = v <> commS "," <> r <> commS "," <> w

inrel :: Note -> Note -> Note
inrel = inrel_ rel

-- Inverse relation

relinv :: Note -> Note
relinv n = n ^: (-1)

-- Unit relation
relunit_ :: Note -> Note
relunit_ n = relunit !: n

relunit :: Note
relunit = "I"

-- Domain
reldomsign :: Note
reldomsign = "Dom"

reldom :: Note -> Note
reldom = fn reldomsign

-- Image
relimgsign :: Note -> Note
relimgsign = fn "Img"

relimg :: Note -> Note
relimg = fn "Img"

-- Composition
relcomp :: Note -> Note -> Note
relcomp = binop $ comm0 "circ"

-- C-k 0M
(●) :: Note -> Note -> Note
(●) = relcomp

-- Preorder
preord :: Note
preord = comm0 "sqsubseteq"

ipreord :: Note
ipreord = comm0 "sqsupseteq"

inpreord_ :: Note -> Note -> Note -> Note
inpreord_ = inrel_

inpreord :: Note -> Note -> Note
inpreord = inpreord_ preord

-- Equivalence Relation
eqrel :: Note
eqrel = comm0 "sim" <> raw "\\mkern-3mu"

ineqrel_ :: Note -> Note -> Note -> Note
ineqrel_ = inpreord_

ineqrel :: Note -> Note -> Note
ineqrel = ineqrel_ eqrel

(.~) :: Note -> Note -> Note
(.~) = ineqrel

-- Equivalence class
eqcl_ :: Note -> Note -> Note
eqcl_ r x = sqbrac x !: r

eqcl :: Note -> Note
eqcl = sqbrac

eqcls :: Note -> Note -> Note
eqcls r x = x <> "/" <> r

-- Partial order
partord :: Note
partord = preord

ipartord :: Note
ipartord = ipreord

-- Poset
posetset :: Note
posetset = "X"

relposet_ :: Note -> Note -> Note
relposet_ = tuple

relposet :: Note
relposet = relposet_ posetset partord

inposet_ :: Note -> Note -> Note -> Note
inposet_ = inpreord_

inposet :: Note -> Note -> Note
inposet = binop partord

iinposet :: Note -> Note -> Note
iinposet = binop ipartord

-- C-k (_
(⊆:) :: Note -> Note -> Note
(⊆:) = inposet

-- C-k )_
(⊇:) :: Note -> Note -> Note
(⊇:) = iinposet

-- Total order
totord :: Note
totord = comm0 "le"

-- maximal element
top :: Note
top = comm0 "top"

-- minimal element
bot :: Note
bot = comm0 "bot"


-- Infimum C-k lb
(⊔) :: Note -> Note -> Note
(⊔) = binop $ comm0 "sqcup"

inf :: Note -> Note
inf = fn "Inf"

-- supremum C-k ub
(⊓) :: Note -> Note -> Note
(⊓) = binop $ comm0 "sqcap"

sup :: Note -> Note
sup = fn "Sup"

-- Lattice
latticeset :: Note
latticeset = posetset

rellat_ :: Note -> Note -> Note
rellat_ = relposet_

rellat :: Note
rellat = rellat_ latticeset partord
