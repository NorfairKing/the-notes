module Statistics.Macro where

import           Types

import           Macro.Math

-- | Statistical model
smod_ :: Note
smod_ = mathfrak "F"

-- | Parameter space
parsp_ :: Note
parsp_ = comm0 "Theta"

-- | Parametric model
parmod_ :: Note
parmod_ = mathfrak "G"
