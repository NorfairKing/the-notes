module MachineLearning.SupervisedLearning.SupportVectorMachines where

import           Notes

import           Geometry.AffineSpaces.Terms
import           LinearAlgebra.VectorSpaces.Terms

import           MachineLearning.SupervisedLearning.Terms

import           MachineLearning.SupervisedLearning.SupportVectorMachines.Macro
import           MachineLearning.SupervisedLearning.SupportVectorMachines.Terms

supportVectorMachinesS :: Note
supportVectorMachinesS = note "support-vector-machines" $ do
    subsection "Support vector machines"
    svmContext
    linearSVM

svmContext :: Note
svmContext = do
    lab supportVectorMachinesDefinitionLabel
    s [supportVectorMachines', " are ", supervisedLearning, " models with associated learning algorithms that are trained to perform binary classification"]

normalVector :: Note
normalVector = ix "normal vector"

linearSVM :: Note
linearSVM = do
    subsubsection "Linear SVM"
    let (b, p, w, x, y) = (vec "b", vec "p", vec "w", vec "x", "y")
        labs = setofs [1, -1]
    s ["Given a dataset of tuples ", m $ tuple x y, " with ", m x, " a ", euclideanVector_, " and ", m $ y ∈ labs]
    s ["Linear ", supportVectorMachines, " find the maximum-margin ", hyperplane_, " that divides the set of points with label ", m 1, " from the points with label ", m (-1)]
    s ["Let the ", hyperplane, " be the following set of points"]
    ma $ setcmpr x (w /.\ x + b =: 0)
    s ["Here ", m w, " is called the ", normalVector, " to the hyperplane", and, m b, " an offset"]
    s ["Note that it is not necessarily a ", ix "unit vector"]

    newline

    s ["If the training data are ", ix "linearly separable", " there exist two ", ix "parallel", " hyperplanes that separate the two classes"]
    todo "linearly separable"
    todo "parallel"
    s [linearSupportVectorMachines, " then try to find the pair of those hyperplanes with the largest distance between the two"]
    s ["These two hyperplanes can be described as follows"]
    ma $ setcmpr x (w /.\ x + b=: 1) <> quad <> setcmpr x (w /.\ x + b =: -1)

    let a = "a"
    s ["Note that we could choose ", m a, and, m (-a), " instead of ", m 1, and, m (-1), " but the latter option ensures that ", m w, " is a unique ", normalVector]

    newline


    s ["Once ", m w, " has been optained, we can classify a point ", m p, " by calculating ", m $ w /.\ p, " and looking at the sign"]
    s ["The sign will give us the label and the magnitude will give us some sense of the confidence with which we classify ", m p]
    de $ do
        s [the, confidence', " ", m conf_, " in the prediction ", m $ y =: sign (w /.\ x /+\ b), " of the label of a data point ", m x, " given a ", normalVector, m w, " is defined as follows"]
        ma $ conf_ =: (pars $ w /.\ x /+\ b) * y

    s ["Given a set of training examples, we find the ", ix "normal vector", m w, " as follows"]
    s ["Finding this hyperplane is equivalent to solving the following optimisation problem"]

    why -- TODO

    nte $ do
        s ["Without loss of generality, we can assume that the desired ", hyperplane, " goes through the ", origin, " given that we use the ", ix "homogenous representation", " of vectors"]
        why
