module MachineLearning.SupervisedLearning.Macro where

import           Types

import           Macro.Tuple


-- * Measurements

-- | Measurement input space
mmis_ :: Note
mmis_ = "X"

-- | Measurement output space
mmos_ :: Note
mmos_ = "Y"

-- * Measurement Spaces

-- | Measurement Space
mms :: Note -> Note -> Note
mms = tuple

-- | Concrete measurement space
mms_ :: Note
mms_ = mms mmis_ mmos_

-- * Loss functions

-- | Concrete loss function
lf_ :: Note
lf_ = "l"
