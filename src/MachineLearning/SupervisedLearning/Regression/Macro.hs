module MachineLearning.SupervisedLearning.Regression.Macro where

import           Types

import           Functions.Application.Macro

-- | Residual sum of squares
rss :: Note -- ^ Beta parameter
    -> Note
rss = fn "RSS"
