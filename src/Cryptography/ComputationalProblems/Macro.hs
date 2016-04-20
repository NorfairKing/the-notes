module Cryptography.ComputationalProblems.Macro where

import           Types

import           Functions.Application.Macro
import           Groups.Macro
import           Macro.MetaMacro
import           Macro.Tuple
import           Probability.Distributions.Macro

-- * Search problems

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

-- * Discrete logarithms

-- | Example group for use with the discrete logarithm problem notation
dlgrp_ :: Note
dlgrp_ = grp (genby "g") grpop_

-- | Discrete logarithm problem for given group. (Use this with the <generator>, operation notation of groups).
dlp :: Note -> Note
dlp = ("DL" .!:)

-- | Discrete logarithm problem for given group in the worst-case.
dlpw :: Note -> Note
dlpw grp = dlp grp .^: "*"

-- | Discrete logarithm problem for given group in the case of the given distribution
dlpd :: Note -- ^ Group
     -> Note -- ^ Distribution
     -> Note
dlpd grp dis = dlp grp .^: dis

-- | Discrete logarithm problem for given group in the average-case.
dlpa :: Note -> Note
dlpa grp = dlpd grp uniformD_
