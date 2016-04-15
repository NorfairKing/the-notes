module Cryptography.ComputationalProblems.Macro where

import           Types

import           Functions.Application.Macro
import           Macro.MetaMacro
import           Macro.Tuple

-- | Search problem
sprob :: Note -- ^ Instance space
      -> Note -- ^ Witness space
      -> Note -- ^ Predicate
      -> Note -- ^ Probability distribution
      -> Note
sprob = quadruple

-- | Instance space
isp_ :: Note
isp_ = mathcal "X"

-- | Witness space
wsp_ :: Note
wsp_ = mathcal "W"

-- | Search space predicate
spred_ :: Note
spred_ = "Q"

-- | Search problem probability distribution
sppd_ :: Note
sppd_ = "P" !: isp_

-- | Concrete search problem
sprob_ :: Note
sprob_ = sprob isp_ wsp_ spred_ sppd_

-- | solution predicate
sol :: Note -> Note -> Note
sol = fn2 spred_
