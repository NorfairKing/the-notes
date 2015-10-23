module MachineLearning.Main (machineLearning) where

import           Notes

import           MachineLearning.Regression         (regression)
import           MachineLearning.SupervisedLearning (supervisedLearning)

machineLearning :: Notes
machineLearning = notes "machine-learning" $
  [
      notesPart "header" (chapter "Machine Learning")
    , supervisedLearning
    , regression
  ]

-- Conditional expected risk
-- total expected risk
-- emperical risk
-- training data
-- test data
-- validation data
-- emperical test error
-- expected risk





