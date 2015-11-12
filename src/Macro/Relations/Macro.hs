module Macro.Relations.Macro where

import           Macro.Math
import           Macro.MetaMacro

import           Macro.Functions.Application

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
