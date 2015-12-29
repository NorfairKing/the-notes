module Macro.Probability.Macro where

import           Types

import           Macro.Index
import           Macro.Math
import           Macro.MetaMacro

import           Functions.Application.Macro
import           Functions.Basics.Macro

import           Probability.Intro.Macro


--[ Probability random variable
prrv :: Note
prrv = "X"

prrvfunc :: Note
prrvfunc = fun prrv univ_ reals

-- Probability value from random variable
prvrv :: Note -> Note
prvrv = fn prrv


--[ Probability distribution function
prdfsign :: Note
prdfsign = "F"

prdfm :: Note -> Note
prdfm n = prdfsign !: n -- probability distribution function modified

prdf :: Note
prdf = prdfm prrv  -- probability distribution function

prd :: Note -> Note
prd = app prdf -- probability distribution at point argument


--[ Probability density function
prdsfsign :: Note
prdsfsign = "f"

prdsfm :: Note -> Note
prdsfm n = prdsfsign !: n --  probability density function modified

prdsf :: Note
prdsf = prdsfm prrv -- probability density function

prds :: Note -> Note
prds = app prdsf -- probability density



--[ Quantile function
prqfsign :: Note
prqfsign = "Q"

prqfm :: Note -> Note
prqfm n = prqfsign !: n

prqf :: Note
prqf = prqfm prrv

prq :: Note -> Note
prq = app prqf


--[ Expected value
prev :: Note -> Note
prev n = "E" <> sqbrac n

prvar :: Note -> Note
prvar n = "Var" <> sqbrac n



--[ Text
salgebra :: Note
salgebra = m (comm0 "sigma") <> "-algebra"

sa :: Note
sa = ix salgebra

--[ Distributions

distributedAs :: Note -> Note -> Note
distributedAs = binop $ comm0 "sim"

(~.) :: Note -> Note -> Note
(~.) = distributedAs

-- Bernoulli

bernoulliD :: Note -> Note
bernoulliD = binomialD 1

bernoulliD_ :: Note
bernoulliD_ = bernoulliD "p"

-- Binomial

binomialD :: Note -> Note -> Note
binomialD = fn2 $ mathcal "B"

binomialD_ :: Note
binomialD_ = binomialD "n" "p"
