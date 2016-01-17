module Statistics.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro

import           Functions.Application.Macro
import           Probability.ProbabilityMeasure.Macro

-- | Statistical model
smod_ :: Note
smod_ = mathfrak "F"

-- | Parameter space
parsp_ :: Note
parsp_ = comm0 "Theta"

-- | Parametric model
parmod_ :: Note
parmod_ = mathfrak "G"

-- | Parameter
par_ :: Note
par_ = theta

-- | Point estimator of parameter
pest :: Note -> Note
pest = hat

-- | Concrete point estimator
pest_ :: Note
pest_ = pest par_


-- | Bias of estimator with respect to the true value
bs :: Note -> Note -> Note
bs n = fn ("bias" !: n)

-- | Standard error, given a point estimator
se :: Note -> Note
se = fn "SE"


-- | Means squared error of estimator
mse :: Note -> Note
mse = fn "MSE"


-- | Probability given a parameter
probm :: Note -> Note -> Note
probm n = prm (prm_ !: n)

-- | Expected value given a parameter
evm :: Note -> Note -> Note
evm n m = "E" !: n <> sqbrac m


-- | Variance given a parameter
varm :: Note -> Note -> Note
varm n m = "Var" !: n <> sqbrac m

-- | Covariance given a parameter
covm :: Note -> Note -> Note -> Note
covm n = fn2 $ "Cov" !: n
