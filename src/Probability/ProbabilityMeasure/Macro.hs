module Probability.ProbabilityMeasure.Macro where

import           Types

import           Macro.Tuple

import           Functions.Application.Macro

import           Probability.Intro.Macro
import           Probability.SigmaAlgebra.Macro

-- * Borel
borelsign :: Note
borelsign = mathcal "B"

borel :: Note -> Note
borel = app borelsign

boreals :: Note
boreals = borel reals


-- * Probability space

-- | Probabilty space given a universe, sigma algebra and probability measure
prsp :: Note -> Note -> Note -> Note
prsp = triple

-- | Concrete probability space
prsp_ :: Note
prsp_ = prsp univ_ sa_ prm_

prbsp :: Note
prbsp = prsp reals boreals prm_


--[ Probability probability measure
prm_ :: Note
prm_ = "P"

--[ Probability
prm :: Note -> Note -> Note
prm = app -- probability with custom measure

prob :: Note -> Note
prob = prm prm_


-- | Mean
mean_ :: Note
mean_ = mu

-- | Variance
variance_ :: Note
variance_ = sigma
