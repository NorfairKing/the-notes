module Probability.SigmaAlgebra.Macro where

import           Types

import           Macro.Tuple

import           Probability.Intro.Macro

-- * Sigma algebra
prsa :: Note
prsa = mathcal "A"


-- * Measurable space

-- | Measurable space given a universe and sigma algebra
mspace :: Note -> Note -> Note
mspace = tuple

-- | Concrete measurable space
mspace_ :: Note
mspace_ = mspace univ prsa

