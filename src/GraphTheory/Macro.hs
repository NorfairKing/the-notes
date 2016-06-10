module GraphTheory.Macro where

import           Types

import           Macro.Tuple

graph_ :: Note
graph_ = "G"

grph :: Note -> Note -> Note
grph = tuple

grph_ :: Note
grph_ = grph vrt_ edg_

vrt_ :: Note
vrt_ = "V"

edg_ :: Note
edg_ = "E"
