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

-- | Worst-case of a problem
spwc :: Note -> Note
spwc = (.^: "*")

-- | Problem in case of the given distribution
spdc :: Note -> Note -> Note
spdc dis = (.^: dis)

-- | Average-case of a problem"
spac :: Note -> Note
spac = spdc uniformD_

-- | Discrete logarithm problem for given group in the worst-case.
dlpw :: Note -> Note
dlpw = spwc . dlp

-- | Discrete logarithm problem for given group in the case of the given distribution
dlpd :: Note -- ^ Distribution
     -> Note -- ^ Group
     -> Note
dlpd dis = spdc dis . dlp

-- | Discrete logarithm problem for given group in the average-case.
dlpa :: Note -> Note
dlpa = spac . dlp


-- | Least significant bit of the discrete logarithm in a given intmod group.
lsbp :: Note -> Note
lsbp n = ("LSB" !: n)
