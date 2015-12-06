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
