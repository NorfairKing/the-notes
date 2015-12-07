module Macro.Topology.Macro where

import           Types

import           Macro.Math
import           Macro.Text

import           Functions.Distances.Macro (dist_, metr_)

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
toppm = dist_

-- Topology Pseudometric Space
toppms :: Note
toppms = toppms_ topset toppm

toppms_ :: Note -> Note -> Note
toppms_ = tuple

-- Topology Metric
topm :: Note
topm = metr_

-- Topology Metric Space
topms :: Note
topms = topms_ topset topm

topms_ :: Note -> Note -> Note
topms_ = tuple


