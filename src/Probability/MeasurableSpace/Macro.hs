module Probability.MeasurableSpace.Macro where

import           Types

import           Macro.Tuple

import           Functions.Application.Macro

import           Probability.Intro.Macro
import           Probability.SigmaAlgebra.Macro

-- * Measurable space

-- | Measurable space given a universe and sigma algebra
mspace :: Note -> Note -> Note
mspace = tuple

-- | Concrete measurable space
mspace_ :: Note
mspace_ = mspace univ_ sa_


-- * Measure

-- | Measure
meas_ :: Note
meas_ = mu

meas :: Note -> Note
meas = fn meas_


-- * Measure space

-- | Measure space given universe, sigma algebra and measure
measp :: Note -> Note -> Note -> Note
measp = triple

-- | Concrete measure space
measp_ :: Note
measp_ = measp univ_ sa_ meas_
