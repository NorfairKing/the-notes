module Cryptography.ComputationalProblems.Macro where

import           Types

import           Macro.MetaMacro

import           Groups.Macro

import           Cryptography.ComputationalProblems.Abstract.Macro

-- * Games
-- * Diffie-Hellman

-- | Computational Diffie-Hellman problem for a given group. (Use this with the <generator>, operation notation of groups).
cdhp :: Note -> Note
cdhp = ("CDH" .^:)

-- | Decisional Diffie-Hellman problem for a given group.
ddhp :: Note -> Note
ddhp = ("DDH" .^:)

-- * Discrete logarithms

-- | Example group for use with the discrete logarithm problem notation
dlgrp_ :: Note
dlgrp_ = grp (genby "g") grpop_

-- | Discrete logarithm problem for given group. (Use this with the <generator>, operation notation of groups).
dlp :: Note -> Note
dlp = ("DL" .^:)

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


-- | Least significant bit of the discrete logarithm in a given finite cyclic group
lsbp :: Note -> Note
lsbp = ("LSB" .^:)
