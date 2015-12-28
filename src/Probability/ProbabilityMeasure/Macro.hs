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
prspace :: Note -> Note -> Note -> Note
prspace = triple

-- | Concrete probability space
prsp :: Note
prsp = prspace univ_ sa_ prpm

prbsp :: Note
prbsp = prspace reals boreals prpm


--[ Probability probability measure
prpm :: Note
prpm = "P"

--[ Probability
probm :: Note -> Note -> Note
probm = app -- probability with custom measure

prob :: Note -> Note
prob = probm prpm

