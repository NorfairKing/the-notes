module MachineLearning.SupervisedLearning.Regression where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Terms
import           LinearAlgebra.VectorSpaces.Terms
import           Probability.ConditionalProbability.Macro
import           Probability.Intro.Macro
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms

import           MachineLearning.SupervisedLearning.Macro
import           MachineLearning.SupervisedLearning.Terms

import           MachineLearning.SupervisedLearning.Regression.Macro
import           MachineLearning.SupervisedLearning.Regression.Terms

regressionS :: Note
regressionS = subsection "Regression" $ do
    intro
    optimalRegression
    linearRegressionSS
    leastSquaresSS
    ridgeRegressionSS

intro :: Note
intro = do
    let x = "X"
        y = "Y"
    s ["Regression is a ", supervisedLearning, " technique"]
    s ["It assumes that the ", inputSpace, is, m (realVecSpace "p"), " and the ", outputSpace, is, m reals]

    s ["It also assumes that the input ", m x, " the output ", m y, " and the noise on the observations ", m mlnv, " can be modelled as ", randomVariables , " as folows"]
    ma $ y =: fn mlm x + mlnv

    homogenousCoondinates

    -- Parametric Statistics: the functional form of the likelihood
    -- P(X, Y|θ) is given; we want to estimate the parameters θ of the likelihood.
    -- Non-Parametric Statistics: we sample X, Y to estimate the likelihood.
    -- Statistical Learning Theory: we minimize the empirical risk directly without estimating the likelihood.
    --
    -- prior: P(model)
    -- likelihood: P(data|model)
    -- posterior: P(model|data)
    -- evidence: P(data)
homogenousCoondinates :: Note
homogenousCoondinates = subsubsection "Homogenous coordinates" $ do
    s ["Often, in the case of ", regression, " it comes in handy for the sake of brevity to transform ", inputFeatures, " to be ", ix "homogenous", " with the following transformation"]
    let p = "p"
    ma $ do
        let x = ("x" !:)
        veclst (x 1) (x p) <> mapsto <> veclist 1 (x 1) (x p)
    s ["Note that this changes the ", inputSpace, " to ", m $ realVecSpace (p + 1)]

optimalRegression :: Note
optimalRegression = subsubsection "Optimal estimate" $ do
    s ["The optimal estimate for the ", hypothesis, " in ", regression, " looks as follows"]
    let x = "x"
        y = "y"
    ma $ fn y x =: ev (y <> mid <> mlmes =: x)
                =: int_ univ_ (y * cprob y (mlmes =: x)) y
    toprove_ "Formulated like this, this would have to hold for _any_ loss function"
    s ["However, that assumes we know ", m $ cprob y (mlmes =: x)]

linearRegressionSS :: Note
linearRegressionSS = subsubsection "Linear Regression" $ do
    let p = "p"
    s ["In ", linearRegression, " the hypothesis class looks as follows"]
    let b = beta
        i = "i"
        j = "j"
        n = "n"
        x = "x"
        y = "y"
    ma $ setcmpr (hyp_ !: b) (b ∈ reals ^ (p + 1)) <> quad <> text "where" <> quad <> pred x =: b !: 0 + sumcmpr (j =: 1) p (x !: j * b !: j)
    s ["... or, with a", homogenous, "representation of", inputFeatures, ".."]
    ma $ pred x =: trans x /.\ b
    s ["For a given parameter vector", m b, ",", m $ b !: 0, "is often called the", intercept', or, bias']

    de $ do
        s ["Using the", quadraticLoss, function, "we define a", costFunction, "called the", residualSumOfSquares', "as the sum of all the losses"]
        s ["Concretely that looks as follows for ", m n, " ", dataPoints]
        ma $ rss b === sumcmpr (i =: 1) n ((pars $ (y !: i) - trans (x !: i) /.\ b) ^ 2)
    let xs = "X"
        ys = "Y"
    s ["If we put all the datapoints in a ", m $ n `times` (pars $ p + 1), matrix, m xs, "and all the labels in a", vector, m ys, ", then this can be written as follows"]
    ma $ rss b =: trans (pars $ ys - xs /.\ b) /.\ (pars $ ys - xs /.\ b)

leastSquaresSS :: Note
leastSquaresSS = subsubsection "Least squares" $ do
    let b = beta
    let xs = "X"
        ys = "Y"
    s ["The so-called method of least squares consists of building a model ", m b, " that minimizes ", m $ rss b]
    thm $ do
        s ["The value of", m b, " that minimizes", m $ rss b, "can be described as follows as long as", m $ trans xs /.\ xs, is, invertible]
        ma $ hat b =: (matinv $ pars $ trans xs /.\ xs) /.\ (trans xs) /.\ ys
        proof $ do
            s ["Differentiating the equation for ", m $ rss b, " with respect to ", m b, " gives us the following"]
            ma $ trans xs /.\ (pars $ ys - xs /.\ b) =: 0
            s ["We can rewrite this to find the value of", m b, "for which", m $ rss b, "reaches its minimum"]
            align_
                [
                  trans xs /.\ (pars $ ys - xs /.\ b) & "" =: 0
                , trans xs /.\ ys - trans xs /.\ xs /.\ b & "" =: 0
                , trans xs /.\ xs /.\ b & "" =: trans xs /.\ ys
                , b & "" =: (matinv $ pars $ trans xs /.\ xs)  /.\ trans xs /.\ ys
                ]
            toprove_ $ s ["We've only proven that this value of ", m b, " gives an extremum for this value, it's not necessarily a minimum yet, prove that too!"]
            -- s ["For invertible", m $ trans xs /.\ xs, "this means that the following value for", m b, "minimizes", m $ rss b]
            -- ma $ hat b =: (matinv $ pars $ trans xs /.\ xs) /.\ (trans x) /.\ ys

    let xsp = xs <> "'"
    s ["The entire prediction", m $ hat ys, "for a given matrix", m xsp, "of", inputFeatures, "is computed as follows"]
    ma $ hat ys =: xsp /.\ hat b

    -- s ["Under the statistical assumption that", noise, m epsilon, "in", measurement, is, additive, and, "has a", normalDistribution, " with a ", mean, " of ", m 0, " and a ", standardDeviation, "of", m sd_, "it follows from the linearity of expectation that the predictions will be off with the same noise"]
    -- ma $ ys =: xs /.\ b + epsilon

    thm $ do
        textbf "Optimality of the least squares estimate"
        newline
        s ["The least squares estimate of the parameter", m b, "has the smallest", variance, " among all linear unbiased estimates"]
        toprove

ridgeRegressionSS :: Note
ridgeRegressionSS = subsubsection "Ridge Regression" $ do
    s ["Ridge regression, like the least squares method, also minimizes a cost function"]
    de $ do
        let xs = "X"
            ys = "Y"
        s ["Let", m xs, "be a", matrix, "of", inputFeatures, and, m ys, "a", matrix, "of labels"]
        s [the, ridgeCost, "is a", costFunction, "defined as follows with a parameter", m lambda]
        let b = beta
            j = "j"
            p = "p"
        ma $ ridge b lambda ===
             rss b
             +
             (lambda * sumcmpr (j =: 1) p (b !: j ^ 2))
        s ["In", matrix, "notation, this can be rewritten as follows"]
        ma $ ridge b lambda =: rss b + lambda * trans b /.\ b

    thm $ do
        let xs = "X"
            ys = "Y"
        let b = beta
            p = "p"
        s ["The value of", m b, " that minimizes", m $ ridge b lambda, "can be described as follows as long as", m $ trans xs /.\ xs + lambda * id (p + 1), is, invertible]
        ma $ hat b =: (matinv $ pars $ trans xs /.\ xs + lambda * id (p + 1)) /.\ (trans xs) /.\ ys
        toprove

    -- SVD of ridge regression solution



