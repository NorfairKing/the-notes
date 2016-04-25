module Cryptography.ComputationalProblems.Macro where

import           Types

import           Functions.Application.Macro
import           Groups.Macro
import           Macro.MetaMacro
import           Macro.Tuple
import           Probability.Distributions.Macro

-- * Problems

-- | Concrete set of problems
probs_ :: Note
probs_ = comm0 "Theta"

-- | Set of solvers for a problem
solvs :: Note -> Note
solvs = (comm0 "Sigma" !:)

-- | Concrete set of solvers
solvs_ :: Note
solvs_ = solvs probl_

-- | Performance set of a problem
perfs :: Note -> Note
perfs = (comm0 "Omega" !:)

perfs_ :: Note
perfs_ = perfs probl_

-- | Performance function
perffsign :: Note
perffsign = "Perf"

perff :: Note -> Note
perff = (perffsign !:)

perff_ :: Note
perff_ = perff probl_

perf :: Note -> Note -> Note
perf p = fn $ perff p

perf_ :: Note -> Note
perf_ = perf probl_

-- * Games

-- ** Deterministic games
gme_ :: Note
gme_ = "g"

plr_ :: Note
plr_ = "w"

-- ** Probabillistic games
gmev_ :: Note
gmev_ = "G"

plrv_ :: Note
plrv_ = "W"

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
sppd_ = probl_ !: isp_

-- | Concrete search problem
sprob_ :: Note
sprob_ = sprob isp_ wsp_ spred_ sppd_

-- | solution predicate
sol :: Note -> Note -> Note
sol = fn2 spred_

-- | Search problem
probl_ :: Note
probl_ = "p"


-- * Distinction problems

dprob :: Note -> Note -> Note
dprob s1 s2 = autoBrackets langle rangle $ s1 <> comm0 "mid" <> s2

dadv :: Note -> Note -> Note -> Note
dadv d = fn2 $ comm0 "Delta" ^: d

dadvs :: Note -> Note -> Note
dadvs = fn2 $ comm0 "Delta"

-- * Diffie-Hellman

-- | Computational Diffie-Hellman problem for a given group. (Use this with the <generator>, operation notation of groups).
cdhp :: Note -> Note
cdhp = ("CDH" .!:)

-- | Decisional Diffie-Hellman problem for a given group.
ddhp :: Note -> Note
ddhp = ("DDH" .!:)

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
