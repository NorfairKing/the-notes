module MachineLearning.Main (machineLearning) where

import           Notes

import           MachineLearning.Regression           (regression)
import           MachineLearning.SupervisedLearning   (supervisedLearning)
import           MachineLearning.UnsupervisedLearning (unsupervisedLearning)

machineLearning :: Notes
machineLearning = notes "machine-learning" $
  [
      notesPart "header" (chapter "Machine Learning")
    , notesPart "learn-definition" learnDefinition
    , supervisedLearning
    , regression
    , unsupervisedLearning
  ]

learnDefinition :: Note
learnDefinition = s ["A computer program is said to learn from experience ", m e, " with respect to some class of tasks ", m t, " and performance measure ", m p, ", if its performance at tasks in ", m t, " as measured by ", m p, " improves with experience"]
  where
    e = "E"
    t = "T"
    p = "P"

-- Conditional expected risk
-- total expected risk
-- emperical risk
-- training data
-- test data
-- validation data
-- emperical test error
-- expected risk





