module Cryptography.ComputationalProblems.Abstract.Macro where

import           Types

import           Macro.MetaMacro

import           Functions.Application.Macro

-- * Problems
probl_ :: Note
probl_ = "p"

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


-- * Cases
-- | Worst-case of a problem
spwc :: Note -> Note
spwc = (.!: "wc")

-- | Problem in case of the given distribution
spdc :: Note -> Note -> Note
spdc dis = (.!: dis)

-- | Average-case of a problem"
spac :: Note -> Note
spac = (.!: "av")

-- | An abstract problem of which the instance space is restricted
restrictedTo :: Note -> Note -> Note
restrictedTo = (!:)
