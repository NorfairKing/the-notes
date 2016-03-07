module DataMining.LargeScaleLearning.Macro where

import           Types

import           Functions.Application.Macro

-- * Regret

-- | Regret sign
regsign :: Note
regsign = "R"

-- | Regret
reg :: Note -> Note
reg = fn regsign

-- | Optimal feasable fixed point
opt :: Note -> Note
opt = fn "OPT"

-- | Average regret
areg :: Note -> Note
areg = fn $ overline regsign
