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
prsp_ = prsp univ_ sa_ prpm

prbsp :: Note
prbsp = prsp reals boreals prpm


--[ Probability probability measure
prpm :: Note
prpm = "P"

--[ Probability
prm :: Note -> Note -> Note
prm = app -- probability with custom measure

prob :: Note -> Note
prob = prm prpm

