module MachineLearning.Main where

import           Notes

import           MachineLearning.SupervisedLearning.Main (supervisedLearningS)
import           MachineLearning.UnsupervisedLearning    (unsupervisedLearningS)

machineLearning :: Note
machineLearning = chapter "Machine Learning" $ do
    note "learn-definition" learnDefinition
    supervisedLearningS
    unsupervisedLearningS
    learningProblemProcess


learnDefinition :: Note
learnDefinition = de $ s ["A computer program is said to learn from experience ", m e, " with respect to some class of tasks ", m t, " and performance measure ", m p, ", if its performance at tasks in ", m t, " as measured by ", m p, " improves with experience"]
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



learningProblemProcess :: Note
learningProblemProcess = do
    s ["Building an intelligent system for supervised learning consists of the following steps"]
    itemize $ do
        item $ "Representation of objects"
        item $ "Definition of a structure"
        item $ "Optimization"
        item $ "Validation"

    ex $ do
        s ["Say you are asked to build a system that takes as input an image of a written digit and is supposed to output which digit it is"]
        s ["In this case, the objects are digits, numbers between 0 and 9, and measurements are the pixel values for an image"]





