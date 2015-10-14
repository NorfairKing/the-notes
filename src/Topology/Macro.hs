module Topology.Macro where

import           Types

import           Macro.Math
import           Macro.Text

-- Topology set
topset :: Note
topset = "X"

-- Topology Topology (Topology on topset)
toptop :: Note
toptop = mathcal "T"


-- Topological space
topsp :: Note
topsp = pars $ cs [topset, toptop]
