module Probability.SigmaAlgebra.Macro where

import           Types

import           Functions.Application.Macro

-- * Sigma algebra

-- | Concrete sigma algebra
sa_ :: Note
sa_ = mathcal "A"


-- * Borel
borelsign :: Note
borelsign = mathcal "B"

borel :: Note -> Note
borel = fn borelsign

boreals :: Note
boreals = borel reals

