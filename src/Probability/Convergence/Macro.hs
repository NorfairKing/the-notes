module Probability.Convergence.Macro where

import           Types

import           Macro.Arrows
import           Macro.Math
import           Macro.MetaMacro

import           Probability.ProbabilityMeasure.Macro

-- * Convergence in probability
convP :: Note -> Note -> Note
convP = binop $ overset prm_ rightarrow

(-%>) :: Note -> Note -> Note
(-%>) = convP

-- * Convergence in distribution
convD :: Note -> Note -> Note
convD = binop $ overset "D" rightarrow

(-@>) :: Note -> Note -> Note
(-@>) = convD

-- * Convergence in quadratic mean
convQM :: Note -> Note -> Note
convQM = binop $ overset "qm" rightarrow

(-#>) :: Note -> Note -> Note
(-#>) = convQM
