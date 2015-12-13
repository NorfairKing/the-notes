module Sets.PointedSets.Macro where

import           Types

import           Macro.MetaMacro
import           Macro.Tuple

-- * Pointed set
pset :: Note -> Note -> Note
pset = tuple

-- * Example
psetset_ :: Note
psetset_ = "X"

psetbase_ :: Note
psetbase_ = "x" !: 0

pset_ :: Note
pset_ = pset psetset_ psetbase_
