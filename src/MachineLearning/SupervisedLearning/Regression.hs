module MachineLearning.SupervisedLearning.Regression where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Geometry.AffineSpaces.Terms
import           LinearAlgebra.VectorSpaces.Terms
import           Probability.ConditionalProbability.Macro
import           Probability.Distributions.Terms
import           Probability.Intro.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Sets.Basics.Terms

import           MachineLearning.SupervisedLearning.Macro
import           MachineLearning.SupervisedLearning.Terms

import           MachineLearning.SupervisedLearning.Regression.Macro
import           MachineLearning.SupervisedLearning.Regression.Terms

regressionS :: Note
regressionS = subsection "Regression" $ do
    intro
    optimalRegressionSS
    linearRegressionSS
    nonlinearRegressionSS
    densityEstimationSS

intro :: Note
intro = do
    let x = "X"
        y = "Y"
        f = "f"
    s ["Regression is a ", supervisedLearning, " technique"]
    s ["It assumes that the ", inputSpace, is, m (realVecSpace "p"), " and the ", outputSpace, is, m reals]
    s ["It also assumes that there exists a function ", m f, " such that labels can be predicted perfectly using", m f, "as follows"]
    ma $ do
        let x = "x"
            y = "y"
        fn y x =: fn f x

    s ["In reality,", measurement, " is not perfect"]
    s ["There is noise on", measurements, "and it is modeled as a", randomVariable, m nois_]
    s ["In this model, ", dataPoints, " can be viewed as ", randomVariables, "drawn from the following distribution"]
    ma $ y =: fn f x + nois_

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

optimalRegressionSS :: Note
optimalRegressionSS = subsubsection "Optimal estimate" $ do
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
    s ["In ", linearRegression, " we assume that there is a perfect linear relation between the labels and the", inputFeatures, "(assuming a homogenous representation of input features)"]
    let x = "x"
        y = "y"
    ma $ fn y x =: trans x * alpha
    s ["If", measurement, "was perfect, we could just draw a", hyperplane, "through the first", m (p + 1), dataPoints, " and find ", m alpha]
    s ["In reality, there is noise on the", measurement]
    s ["Assuming that", noise, m epsilon, "in", measurement, is, additive, and, "has a", normalDistribution, "with a", mean, "of", m 0, "and a", standardDeviation, "of", m sd_, ", we can model", dataPoints, "as normally distributed", randomVariables]
    let x = "x"
        y = "y"
    ma $ fn y x =: trans x * alpha + epsilon
    -- ma $ ys =: xs /.\ b + epsilon
    s ["As such, the hypothesis class looks as follows"]
    let b = beta
        i = "i"
        j = "j"
        n = "n"
    ma $ setcmpr (hyp_ !: b) (b ∈ reals ^ (p + 1))
         <> quad <> text "where" <> quad <>
         pred x =: b !: 0 + sumcmpr (j =: 1) p (x !: j * b !: j)
         =: trans x /.\ b
    s ["For a given parameter vector", m b, ",", m $ b !: 0, "is often called the", intercept', or, bias']

    de $ do
        s ["Using the", quadraticLoss, function, "we define a", costFunction, "called the", residualSumOfSquares', "as the sum of all the losses"]
        s ["Concretely that looks as follows for ", m n, " ", dataPoints]
        ma $ rss b === sumcmpr (i =: 1) n ((pars $ (y !: i) - trans (x !: i) /.\ b) ^ 2)
    let xs = "X"
        ys = "Y"
    s ["If we put all the datapoints in a ", m $ n `times` (pars $ p + 1), matrix, m xs, "and all the labels in a", vector, m ys, ", then this can be written as follows"]
    ma $ rss b =: trans (pars $ ys - xs /.\ b) /.\ (pars $ ys - xs /.\ b)

    leastSquaresSS
    ridgeRegressionSS
    lassoRegressionSS
    generalRidgeRegression


leastSquaresSS :: Note
leastSquaresSS = do
    let b = beta
    let xs = "X"
        ys = "Y"
    s ["The so-called method of least squares consists of building a model ", m b, " that minimizes ", m $ rss b]
    thm $ do
        s ["The value of", m b, " that minimizes", m $ rss b, "can be described as follows as long as", m $ trans xs /.\ xs, is, invertible]
        ma $ hat b =: (matinv $ pars $ trans xs /.\ xs) /.\ (trans xs) /.\ ys
        proof $ do
            s ["Differentiating the equation for ", m $ rss b, " with respect to ", m b, " gives us the following"]
            let b = beta
                i = "i"
                j = "j"
                k = "k"
                n = "n"
                p = "p"
                x = "x"
                y = "y"
            aligneqs
                (partiald (sumcmpr (i =: 1) n ((pars $ (y !: i) - trans (x !: i) /.\ b) ^ 2)) (b !: j))
                [
                    sumcmpr (i =: 1) n (partiald ((pars $ (y !: i) - trans (x !: i) /.\ b) ^ 2) (b !: j))
                  , sumcmpr (i =: 1) n (2 * (pars $ (y !: i) - trans (x !: i) /.\ b)
                                     * partiald (pars $ (y !: i) - trans (x !: i) /.\ b) (b !: j))
                  , 2 * sumcmpr (i =: 1) n ((pars $ (y !: i) - trans (x !: i) /.\ b)
                                         * (pars $ - partiald (trans (x !: i) /.\ b) (b !: j)))
                  , 2 * sumcmpr (i =: 1) n ((pars $ (y !: i) - trans (x !: i) /.\ b)
                                         * (pars $ - partiald (sumcmpr (k =: 0) p (xs !: cs [i, k]) * (b !: k)) (b !: j)))
                  , 2 * sumcmpr (i =: 1) n ((pars $ - (xs !: cs [i, j])) * (pars $ (y !: i) - trans (x !: i) /.\ b))
                  , 2 * sumcmpr (i =: 1) n ((pars $ - (xs !: cs [i, j])) * (pars $ (y !: i) - sumcmpr (k =: 0) p (xs !: cs [i, k]) * (b !: k)))
                  , 2 * sumcmpr (i =: 1) n ((pars $ - (xs !: cs [i, j])) * (pars $ (y !: i) - (pars $ xs  /.\ b) !: i))
                  , 2 * sumcmpr (i =: 1) n ((pars $ - (trans xs !: cs [j, i])) * (pars $ (y !: i) - (pars $ xs  /.\ b) !: i))
                  , 2 * sumcmpr (i =: 1) n ((pars $ - (trans xs !: cs [j, i])) * (pars $ (y !: i) - xs  /.\ b) !: i)
                  , 2 * (pars $ - (trans xs) /.\ (pars $ ys - xs /.\ b)) !: j
                ]
            s ["For the minimizing value of", m beta, ", this expression must equal zero"]
            ma $ trans xs /.\ (pars $ ys - xs /.\ b) =: 0
            align_
                [
                  trans xs /.\ (pars $ ys - xs /.\ b) & "" =: 0
                , trans xs /.\ ys - trans xs /.\ xs /.\ b & "" =: 0
                , trans xs /.\ xs /.\ b & "" =: trans xs /.\ ys
                , b & "" =: (matinv $ pars $ trans xs /.\ xs)  /.\ trans xs /.\ ys
                ]

            s ["To prove that this value of", m b, "really does give a minimum value for", m $ rss b, "we still have to prove that the second derivative with respect to", m $ beta !: j, "is positive in every direction (for every j)"]
            aligneqs
                (partiald
                    (2 * sumcmpr (i =: 1) n ((pars $ - (xs !: cs [i, j])) * (pars $ (y !: i) - sumcmpr (k =: 0) p (xs !: cs [i, k]) * (b !: k))))
                    (b !: j))
                [
                    2 * sumcmpr (i =: 1) n (partiald ((pars $ - (xs !: cs [i, j])) * (pars $ (y !: i) - sumcmpr (k =: 0) p (xs !: cs [i, k]) * (b !: k)))
                                            (b !: j))
                  , 2 * sumcmpr (i =: 1) n ((pars $ - (xs !: cs [i, j])) * partiald (pars $ (y !: i) - sumcmpr (k =: 0) p (xs !: cs [i, k]) * (b !: k))
                                                                            (b !: j))
                  , 2 * sumcmpr (i =: 1) n ((pars $ - (xs !: cs [i, j])) * (pars $ - sumcmpr (k =: 0) p (partiald ((xs !: cs [i, k]) * (b !: k)) (b !: j))))
                  , 2 * sumcmpr (i =: 1) n ((pars $ - (xs !: cs [i, j])) * (pars $ - (xs !: cs [i, j])))
                  , 2 * sumcmpr (i =: 1) n ((xs !: cs [i, j]) ^ 2)
                ]

    let xsp = xs <> "'"
    s ["The entire prediction", m $ hat ys, "for a given matrix", m xsp, "of", inputFeatures, "is computed as follows"]
    ma $ hat ys =: xsp /.\ hat b

    thm $ do
        s [m $ hat b, " is an unbiased estimation of", m alpha]
        todo "define unbiased estimation"
        proof $ do
            aligneqs
                (ev $ hat b)
                [
                    ev $ (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ ys
                  , ev $ (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ (pars $ xs /.\ alpha + nois_)
                  , ev $ (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ xs /.\ alpha
                       + (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_
                  , ev $ alpha + (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_
                  , ev alpha + ev ((matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_)
                  , alpha + (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ ev nois_
                  , alpha + (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ 0
                  , alpha
                ]
            s ["Note that all but", m nois_, "is constant in the above derivation and that we use the assumption that the", expectedValue, "of the", noise, "is", m 0]
            refs [
                expectationOfConstantTheoremLabel
              , linearityOfExpectationTheoremLabel
              ]

    thm $ do
        let p = "p"
        ma $ (var $ hat b) =: (var_ ^ 2) * (matinv $ pars $ trans xs /.\ xs)
        proof $ do
            aligneqs
                (var $ hat b)
                [
                  ev ((hat b) ^ 2) - (ev (hat b)) ^ 2
                , ev ((matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ ys) - alpha ^ 2
                , ev (pars $ ((matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ (pars $ xs /.\ alpha + nois_)) ^ 2) - alpha ^ 2
                , ev ((pars $ alpha + ((matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_)) ^ 2) - alpha ^ 2
                , ev (alpha ^ 2
                    + 2 * alpha * ((matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_)
                    + (pars $ (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_) ^ 2)
                  - alpha ^ 2
                , ev (alpha ^ 2)
                  + 2 * alpha * ((matinv $ pars $ trans xs /.\ xs) /.\ trans xs) * ev nois_
                  + ev ((pars $ (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_) ^ 2)
                  - alpha ^ 2
                , cancel (alpha ^ 2)
                  + cancel (2 * alpha * ((matinv $ pars $ trans xs /.\ xs) /.\ trans xs) * 0)
                  + ev ((pars $ (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_) ^ 2)
                  - cancel (alpha ^ 2)
                , ev $ (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_
                    /.\ trans nois_ /.\ xs /.\ trans (matinv $ pars $ trans xs /.\ xs)
                , (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\
                  ev (nois_ /.\ trans nois_)
                  /.\ xs /.\ trans (matinv $ pars $ trans xs /.\ xs)
                , (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\
                  (var_ ^ 2) * id (p + 1)
                  /.\ xs /.\ trans (matinv $ pars $ trans xs /.\ xs)
                , (var_ ^ 2) *
                  cancel (matinv $ pars $ trans xs /.\ xs)
                  /.\ cancel (pars $ trans xs /.\ xs)
                  /.\ trans (matinv $ pars $ trans xs /.\ xs)
                , (var_ ^ 2) * trans (matinv $ pars $ trans xs /.\ xs)
                , (var_ ^ 2) * (matinv $ pars $ trans xs /.\ xs)
                ]
            refs [
                expectationOfConstantTheoremLabel
              , linearityOfExpectationTheoremLabel
              , varianceInTermsOfExpectationTheoremLabel
              , matrixTimesTransposeIsSymmetricTheoremLabel
              , inverseOfSymmetricMatrixIsSymmetricTheoremLabel
              ]
            s ["Here we used", m $ ev (nois_ /.\ trans nois_) =: var_ ^ 2 * id (p + 1)]
            why

    thm $ do
        textbf "Optimality of the least squares estimate"
        newline
        s ["The least squares estimate of the parameter", m b, "has the smallest", variance, " among all linear unbiased estimates"]
        toprove

ridgeRegressionSS :: Note
ridgeRegressionSS = do
    s ["Ridge regression, like the least squares method, also minimizes a cost function"]
    de $ do
        let xs = "X"
            ys = "Y"
        s ["Let", m xs, "be a", matrix, "of", inputFeatures, and, m ys, "a", matrix, "of labels"]
        s [the, ridgeCost', "is a", costFunction, "defined as follows with a parameter", m lambda]
        let b = beta
            j = "j"
            p = "p"
        ma $ ridge b lambda ===
             rss b
             +
             lambda * sumcmpr (j =: 1) p (b !: j ^ 2)
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


lassoRegressionSS :: Note
lassoRegressionSS = do
    s ["Least absolute shrinkage and selector operator (LASSO) regression, like the other methods above, also minimizes a cost function"]
    de $ do
        let xs = "X"
            ys = "Y"
        s ["Let", m xs, "be a", matrix, "of", inputFeatures, and, m ys, "a", matrix, "of labels"]
        s [the, lASSOCost', "is a", costFunction, "defined as follows with a parameter", m lambda]
        let b = beta
            j = "j"
            p = "p"
        ma $ ridge b lambda ===
             rss b
             +
             lambda * sumcmpr (j =: 1) p (abs $ b !: j)


generalRidgeRegression :: Note
generalRidgeRegression = do
    let q = "q"
    s ["Ridge regression can be generalized to have a shrinkage term parametrized by ", m q]
    de $ do
        s ["The generalized ", ridgeCost, " is a cost function with parameter ", m q]
        let b = beta
            j = "j"
            p = "p"
        ma $ ridge b lambda ===
             rss b
             +
             lambda * sumcmpr (j =: 1) p (abs (b !: j) ^ q)

nonlinearRegressionSS :: Note
nonlinearRegressionSS = subsection "Nonlinear Regression" $ do
    s ["The idea of", nonlinearRegression, "is to apply a nonlinear", transformation, "to the", inputFeatures, and, outputFeatures, "and performing", linearRegression, "on the result"]

    let b = beta
        f = "f"
        j = "j"
        p = "p"
        x = "x"
    s ["Given a nonlinear transformation ", m $ fun f (reals ^ p) reals, the, hypothesisClass, "of",the, nonlinearRegression, "method is the following set"]
    ma $ setcmpr (hyp_ !: b) (b ∈ reals ^ (p + 1)) <> quad <> text "where" <> quad <> pred x =: sumcmpr (j =: 1) p (fn f x * b !: j)


densityEstimationSS :: Note
densityEstimationSS = subsection "Density estimation" $ do
    lab densityEstimationDefinitionLabel
    s ["Recall the optimal solution to the", regression, "problem"]
    s ["In", densityEstimation_, "the goal is to estimate", m $ cprob "y" ("X" =: "x")]
    s ["That is the", probability, "that a", dataPoint, m "x", "gets labeled as", m "y", "given its features"]
    maximumLikelyhoodEstimationSS

maximumLikelyhoodEstimationSS :: Note
maximumLikelyhoodEstimationSS = do
    de $ do
        s [maximumLikelihoodEstimation', "is a technique used in", densityEstimation]
        let f = "f"
            x = "X"
        s ["Given a", set, "of", probabilityDensityFunctions, ", indexed by some  parameter", m theta, "and a", dataset, ", ", maximumLikelihoodEstimation, " works by selecting the", probabilityDensityFunction, m f, "that maximizes the likelihood that the observed", dataPoints, "are to occur", "given that they come from a distribution with", probabilityDensityFunction, m f]
        ma $ hat theta =: argmax theta (cprob x theta)

bayesianLearningSS :: Note
bayesianLearningSS = do
    todo "bayesian learning"
