module Statistics.Macro where

import           Types

import           Macro.Math

import           Functions.Application.Macro

-- | Statistical model
smod_ :: Note
smod_ = mathfrak "F"

-- | Parameter space
parsp_ :: Note
parsp_ = comm0 "Theta"

-- | Parametric model
parmod_ :: Note
parmod_ = mathfrak "G"

-- | Parameter
par_ :: Note
par_ = theta

-- | Point estimator of parameter
pest :: Note -> Note
pest = hat

-- | Concrete point estimator
pest_ :: Note
pest_ = pest par_


-- | Bias of estimator
bs :: Note -> Note
bs = fn "bias"

