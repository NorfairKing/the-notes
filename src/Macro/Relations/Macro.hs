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
preordset_ :: Note
preordset_  = "X"

preord_ :: Note
preord_ = commS "sqsubseteq" <> " "

ipreord_ :: Note
ipreord_ = commS "sqsupseteq" <> " "

relpreord :: Note -> Note -> Note
relpreord = tuple

relpreord_ :: Note
relpreord_ = relpreord preordset_ preord_

inpreord :: Note -> Note -> Note -> Note
inpreord = inrel_

inpreord_ :: Note -> Note -> Note
inpreord_ = inpreord preord_
