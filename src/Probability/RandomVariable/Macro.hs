module Probability.RandomVariable.Macro where

import           Types

import           Prelude                                  (error, sequence_)

import           Macro.Math
import           Macro.MetaMacro
import           Macro.Text
import           Macro.Tuple

import           Functions.Application.Macro
import           Functions.Basics.Macro

import           Probability.ConditionalProbability.Macro
import           Probability.Intro.Macro
import           Probability.ProbabilityMeasure.Macro

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

-- * Probability distribution
-- | Set of probability distributions of Y-rvs
prdss :: Note -> Note
prdss = (^ "pd")

-- | Probability distribution given the random variable that it is of
--
-- > prdis_ "X"
-- >>> Pr_{X}
prdis_ :: Note -> Note
prdis_ x = prm_ ^: x

-- | The application of such a probability distribution
-- > prdis "X" "a"
-- >>> Pr_{X}(a)
prdis :: Note -> Note -> Note
prdis = prm . prdis_

-- Probability distribution given the random variables that it is of
prdiss_ :: [Note] -> Note
prdiss_ = prdis_ . cs

prdiss :: [Note] -> Note -> Note
prdiss = prm . prdiss_

-- * Random variable tuple
rtup :: Note -> Note -> Note
rtup = tuple

-- * Cumulative distribution function
dfsign_ :: Note
dfsign_ = "F"

-- | A cumulative distribution function given a random varable
df :: Note -> Note
df n = dfsign_ !: n

-- | A concrete cumulative distribution function
df_ :: Note
df_ = df rv_  -- probability distribution function

-- | Cumulative distribution at point argument with modified symbol
prdm :: Note -> Note -> Note
prdm = fn

-- | The cumulative distribution at point argument
prd :: Note -> Note
prd = prdm df_



-- * Density function
dsfsign_ :: Note
dsfsign_ = "f"

dsf :: Note -> Note
dsf n = dsfsign_ !: n --  probability density function modified

dsf_ :: Note
dsf_ = dsf rv_ -- probability density function

prds :: Note -> Note
prds = prdsm dsf_ -- probability density

-- | Probabilty density at point argument with modified symbol
prdsm :: Note -> Note -> Note
prdsm = fn


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

-- | Expected value
ev :: Note -> Note
ev n = "E" <> sqbrac n

-- | Expected value over given random variable
evm :: Note -> Note -> Note
evm m n = "E" !: m <> sqbrac n

-- | Expected value over given random variables
evms :: [Note] -> Note -> Note
evms ms = evm (sequence_ ms)
-- FIXME move this? to statistics

-- | Mean
mn :: Note -> Note
mn = ev

-- | Concrete mean
mn_ :: Note
mn_ = mu

-- * Covariance

-- | Covariance of two random variables
cov :: Note -> Note -> Note
cov = fn2 "Cov"

-- * Variance

-- | Variance
var :: Note -> Note
var n = "Var" <> sqbrac n

-- | Concrete variance
var_ :: Note
var_ = sd_ ^: 2

-- * Correlation

-- | Correlation of two random variables
cor :: Note -> Note -> Note
cor = fn2 "Cor"

-- * Standard deviation

-- | Concrete standard deviation
sd_ :: Note
sd_ = sigma


-- * Joint distribution
probs :: [Note] -> Note
probs vs = prob $ cs vs

cprobs :: Note -> [Note] -> Note
cprobs n [] = prob n
cprobs v cvs = cprob v (cs cvs)

cprobss :: [Note] -> [Note] -> Note
cprobss [] [] = error "Can't have conditional probability of no variables"
cprobss n [] = probs n
cprobss vs cvs = cprob (cs vs) (cs cvs)


-- * Copies

-- | Independent copy
icop :: Note -- Random variable
     -> Note -- Power
     -> Note
icop = (^:)

-- | Clone
clon :: Note -- Random variable
     -> Note -- Power
     -> Note
clon x q = x ^: (sqbrac q)

-- * Statistical distance
statd :: Note -> Note -> Note
statd = fn2 delta

-- * Empirical

-- | Empirical mean
emean :: Note -> Note
emean = comm1 "overline"

-- TODO Empirical variance
