module MachineLearning.UnsupervisedLearning (
      unsupervisedLearning
    ) where

import           Notes

unsupervisedLearning :: Note
unsupervisedLearning = note "unsupervised-learning" body

body :: Note
body = do
    section "Unsupervised Learning"
    learningProblem

learningProblem :: Note
learningProblem = do
    subsection "The learning problem"

