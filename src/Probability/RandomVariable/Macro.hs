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
rvfunc_ :: Note
rvfunc_ = fun rv_ univ_ reals
-- FIXME fix variable name

-- | Probability value from random variable
vrv :: Note -> Note
vrv = fn rv_
-- FIXME fix variable name

-- * Distribution function
dfsign_ :: Note
dfsign_ = "F"

df :: Note -> Note
df n = dfsign_ !: n -- probability distribution function modified

df_ :: Note
df_ = df rv_  -- probability distribution function

prd :: Note -> Note
prd = app df_ -- probability distribution at point argument


-- * Density function
dsfsign_ :: Note
dsfsign_ = "f"

dsf :: Note -> Note
dsf n = dsfsign_ !: n --  probability density function modified

dsf_ :: Note
dsf_ = dsf rv_ -- probability density function

prds :: Note -> Note
prds = app dsf_ -- probability density


-- * Quantile function
qfsign_ :: Note
qfsign_ = "Q"

prqfm :: Note -> Note
prqfm n = qfsign_ !: n

prqf :: Note
prqf = prqfm rv_

prq :: Note -> Note
prq = app prqf

-- * Expected value
ev :: Note -> Note
ev n = "E" <> sqbrac n
-- FIXME move this

-- | Mean
mn :: Note -> Note
mn = ev

-- | Concrete mean
mn_ :: Note
mn_ = mu


-- * Variance

-- | Variance
var :: Note -> Note
var n = "Var" <> sqbrac n

-- | Concrete variance
var_ :: Note
var_ = sigma

-- * Standard deviation

-- | Concrete standard deviation
sd_ :: Note
sd_ = var_ ^: 2
