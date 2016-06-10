module MachineLearning.SupervisedLearning.Regression.Macro where

import           Types

import           Functions.Application.Macro

-- | Concrete noise modeling random variable
nois_ :: Note
nois_ = epsilon

-- | Residual sum of squares
rss :: Note -- ^ Beta parameter
    -> Note
rss = fn "RSS"

-- | Ridge cost
ridge :: Note -- ^ Beta parameter
      -> Note -- ^ Lambda parameter
      -> Note
ridge = fn2 "Ridge"

lasso :: Note -- ^ Beta parameter
      -> Note -- ^ Lambda parameter
      -> Note
lasso = fn2 "Lasso"
