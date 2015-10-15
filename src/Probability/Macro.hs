module Probability.Macro where

import           Types

import           Macro.Index
import           Macro.Math

import           Functions.Macro
import           Sets.Macro

--[ Probability universe
pruniv :: Note
pruniv = setuniv


--[ Measurable space
prmspace :: Note -> Note -> Note
prmspace m n = m <> ", " <> n

prms :: Note
prms = prmspace pruniv prsa


--[ Probability space
prspace :: Note -> Note -> Note -> Note
prspace m n o = m <> ", " <> n <> ", " <> o

prsp :: Note
prsp = prspace pruniv prsa prpm

prbsp :: Note
prbsp = prspace reals boreals prpm


--[ Probability Sigma Algebra
prsa :: Note
prsa = mathcal "A"


--[ Probability probability measure
prpm :: Note
prpm = "P"


--[ Probability
probm :: Note -> Note -> Note
probm = funapp -- probability with custom measure

prob :: Note -> Note
prob = probm prpm


--[ Conditional probability
cprob :: Note -> Note -> Note
cprob n m = prob $ n <> mid <> m


--[ Probability random variable
prrv :: Note
prrv = "X"

prrvfunc :: Note
prrvfunc = fun prrv pruniv reals


--[ Probability distribution function
prdfsign :: Note
prdfsign = "F"

prdfm :: Note -> Note
prdfm n = prdfsign !: n -- probability distribution function modified

prdf :: Note
prdf = prdfm prrv  -- probability distribution function

prd :: Note -> Note
prd = funapp prdf -- probability distribution at point argument


--[ Probability density function
prdsfsign :: Note
prdsfsign = "f"

prdsfm :: Note -> Note
prdsfm n = prdsfsign !: n --  probability density function modified

prdsf :: Note
prdsf = prdsfm prrv -- probability density function

prds :: Note -> Note
prds = funapp prdsf -- probability density


--[ Borel
borelsign :: Note
borelsign = mathcal "B"

borel :: Note -> Note
borel = funapp borelsign

boreals :: Note
boreals = borel reals


--[ Quantile function
prqfsign :: Note
prqfsign = "Q"

prqfm :: Note -> Note
prqfm n = prqfsign !: n

prqf :: Note
prqf = prqfm prrv

prq :: Note -> Note
prq = funapp prqf


--[ Expected value
prev :: Note -> Note
prev n = "E" <> sqbrac n

prvar :: Note -> Note
prvar n = "Var" <> sqbrac n



--[ Text
universe :: Note
universe = ix "universe"

universe_ :: Note
universe_ = universe <> " " <> m pruniv

salgebra :: Note
salgebra = m (comm0 "sigma") <> "-algebra"

sa :: Note
sa = ix salgebra

--sa_ :: Note
-- sa_ = sa <> " " <> m prsa
