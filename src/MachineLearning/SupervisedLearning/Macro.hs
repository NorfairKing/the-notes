module MachineLearning.SupervisedLearning.Macro where

import           Types

import           Macro.MetaMacro
import           Macro.Tuple

import           Functions.Application.Macro

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

-- * Hypotheses

-- | Concrete hypothesis
hyp_ :: Note
hyp_ = "h"

-- | Prediction
pred :: Note -> Note
pred = fn hyp_

-- | Concrete hypothesis class
hypc_ :: Note
hypc_ = mathcal "H"

-- * Loss functions

-- | Concrete loss function
lf_ :: Note
lf_ = "l"

loss :: Note -> Note -> Note
loss = fn2 lf_

-- * Datasets

-- | Full dataset
ds_ :: Note
ds_ = mathcal "Z"

-- | Training data
trds_ :: Note
trds_ = ds_ !: "train"

-- | Validation data
vds_ :: Note
vds_ = ds_ !: "validation"

-- | Test data
tds_ :: Note
tds_ = ds_ !: "test"

-- * Risk

-- ** Conditional expected risk

-- | Risk function
risk_ :: Note
risk_ = "R"

-- | Conditional expected risk, given:
cer :: Note -- ^ Hypothesis
    -> Note -- ^ Loss function
    -> Note -- ^ Distribution of the input space
    -> Note
cer = fn3 risk_

-- | Concrede conditional expected risk
cer_ :: Note
cer_ = cer hyp_ lf_ mmis_

-- ** Total expected risk
ter :: Note -- ^ Hypothesis
    -> Note -- ^ Loss function
    -> Note
ter = fn2 risk_

-- | Total expected risk
ter_ :: Note
ter_ = ter hyp_ lf_

