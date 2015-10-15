module Macro.Topology.Macro where

import           Types

import           Macro.Math
import           Macro.Text

import           Macro.Functions.Macro (fundist, funm)

-- Topology set
topset :: Note
topset = "X"

-- Topology Topology (Topology on topset)
toptop :: Note
toptop = comm0 "tau"

-- Topological space
topsp :: Note
topsp = pars $ cs [topset, toptop]

-- Topology Pseudometric
toppm :: Note
toppm = fundist

-- Topology Pseudometric Space
toppms :: Note
toppms = toppms_ topset toppm

toppms_ :: Note -> Note -> Note
toppms_ = tuple

-- Topology Metric
topm :: Note
topm = funm

-- Topology Metric Space
topms :: Note
topms = topms_ topset topm

topms_ :: Note -> Note -> Note
topms_ = tuple


