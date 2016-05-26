module Probability.MeasurableSpace.Macro where

import           Types

import           Macro.Tuple

import           Probability.Intro.Macro
import           Probability.SigmaAlgebra.Macro

-- * Measurable space

-- | Measurable space given a universe and sigma algebra
mspace :: Note -> Note -> Note
mspace = tuple

-- | Concrete measurable space
mspace_ :: Note
mspace_ = mspace univ_ sa_


