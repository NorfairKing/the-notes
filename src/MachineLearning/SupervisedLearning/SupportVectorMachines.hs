module MachineLearning.SupervisedLearning.SupportVectorMachines where

import           Notes

import           Geometry.AffineSpaces.Terms
import           LinearAlgebra.VectorSpaces.Terms

import           MachineLearning.SupervisedLearning.Terms

import           MachineLearning.SupervisedLearning.SupportVectorMachines.Terms

supportVectorMachinesS :: Note
supportVectorMachinesS = note "support-vector-machines" $ do
    subsection "Support vector machines"
    svmContext
    linearSVM

svmContext :: Note
svmContext = do
    lab supportVectorMachinesDefinitionLabel
    s [supportVectorMachines', " are ", supervisedLearning, " models with associated learning algorithms that analyse data and recognize patterns"]

linearSVM :: Note
linearSVM = do
    let (x, y) = (vec "x", "y")
        labs = setofs [1, -1]
    s ["Given a dataset of tuples ", m $ tuple x y, " with ", m x, " a ", euclideanVector_, " and ", m $ y ∈ labs]
    s ["Linear ", supportVectorMachines, " find the maximum-margin ", hyperplane_, " that divides the set of points with label ", m 1, " from the points with label ", m (-1)]
    -- TODO explain what that is.


