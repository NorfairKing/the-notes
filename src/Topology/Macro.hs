module Topology.Macro where

import           Types

import           Macro.Math
import           Macro.Text

-- Topology set
topset :: Note
topset = "X"

-- Topology Topology (Topology on topset)
toptop :: Note
toptop = comm0 "tau"


-- Topological space
topsp :: Note
topsp = pars $ cs [topset, toptop]
