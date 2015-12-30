module Probability.RandomVariable.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro

import           Functions.Application.Macro
import           Functions.Basics.Macro

import           Probability.Intro.Macro

-- * Random variable

-- | Concrete random variable
rv_ :: Note
rv_ = "X"
-- FIXME fix variable name

-- | Function declaration for concrete random variable
prrvfunc :: Note
prrvfunc = fun rv_ univ_ reals
-- FIXME fix variable name

-- | Probability value from random variable
prvrv :: Note -> Note
prvrv = fn rv_
-- FIXME fix variable name

-- * Distribution function
prdfsign :: Note
prdfsign = "F"

prdfm :: Note -> Note
prdfm n = prdfsign !: n -- probability distribution function modified

prdf :: Note
prdf = prdfm rv_  -- probability distribution function

prd :: Note -> Note
prd = app prdf -- probability distribution at point argument


-- * Density function
prdsfsign :: Note
prdsfsign = "f"

prdsfm :: Note -> Note
prdsfm n = prdsfsign !: n --  probability density function modified

prdsf :: Note
prdsf = prdsfm rv_ -- probability density function

prds :: Note -> Note
prds = app prdsf -- probability density


-- * Quantile function
prqfsign :: Note
prqfsign = "Q"

prqfm :: Note -> Note
prqfm n = prqfsign !: n

prqf :: Note
prqf = prqfm rv_

prq :: Note -> Note
prq = app prqf

-- * Expected value
prev :: Note -> Note
prev n = "E" <> sqbrac n
-- FIXME move this

-- * Variance
prvar :: Note -> Note
prvar n = "Var" <> sqbrac n
-- FIXME move this
