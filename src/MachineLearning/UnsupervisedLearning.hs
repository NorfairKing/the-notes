module MachineLearning.UnsupervisedLearning (
    unsupervisedLearning
  ) where

import           Notes

unsupervisedLearning :: Notes
unsupervisedLearning = notesPart "unsupervised-learning" body

body :: Note
body = do
  section "Unsupervised Learning"
  learningProblem

learningProblem :: Note
learningProblem = do
  subsection "The learning problem"

