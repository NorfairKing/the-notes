module MachineLearning.SupervisedLearning.Regression where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Geometry.AffineSpaces.Terms
import           LinearAlgebra.VectorSpaces.Terms
import           Probability.ConditionalProbability.Macro
import           Probability.Distributions.Terms
import           Probability.Independence.Terms
import           Probability.Intro.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Sets.Basics.Terms
import           Statistics.Macro
import           Statistics.Terms

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
    s ["Regression is a", supervisedLearning, "technique"]
    let p = "p"
    s ["It assumes that the", inputSpace, is, m $ realVecSpace p, "for some", m $ natural p, "and the", outputSpace, is, m reals]
    s ["It also assumes that there exists a", function, m f, " such that labels can be predicted perfectly using", m f, "as follows"]
    ma $ do
        let x = "x"
            y = "y"
        fn y x =: fn f x

    s ["In reality", measurement, "is not perfect"]
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
    s ["Often, in the case of", regression, "it comes in handy for the sake of brevity to transform", inputFeatures, " to be", homogenous, " with the following transformation"]
    let p = "p"
    ma $ do
        let x = ("x" !:)
        veclst (x 1) (x p) <> mapsto <> veclist 1 (x 1) (x p)
    s ["Note that this changes the", inputSpace, "to", m $ realVecSpace (p + 1)]

optimalRegressionSS :: Note
optimalRegressionSS = subsubsection "Optimal estimate" $ do
    s ["The optimal", hypothesis, "in", regression, "looks as follows"]
    let x = "x"
        y = "y"
    ma $ fn y x =: ev (y <> mid <> mlmes =: x)
                =: int_ univ_ (y * cprob y (mlmes =: x)) y
    toprove_ "Formulated like this, this would have to hold for _any_ loss function"
    s ["However, that assumes we know ", m $ cprob y (mlmes =: x)]

linearRegressionSS :: Note
linearRegressionSS = subsubsection "Linear Regression" $ do
    let p = "p"
    s ["In", linearRegression, "we assume that there is a perfect linear relation between the labels and the", inputFeatures, "(assuming a", homogenous, "representation of input features)"]
    let x = "x"
        y = "y"
    ma $ fn y x =: trans x * alpha
    s ["If", measurement, "was perfect, we could just draw a", hyperplane, "through the first", m (p + 1), dataPoints, " and find ", m alpha]
    s ["In reality, there is noise on the", measurement]
    s ["Assuming that", noise, m epsilon, "in", measurement, is, additive, and, "has a", normalDistribution, "with a", mean, "of", m 0, "and a", standardDeviation, "of", m sd_, ", we can model", dataPoints, "as normally distributed", randomVariables]
    let x = "x"
        y = "y"
    ma $ fn y x =: trans x * alpha + epsilon

    s ["As such, the", hypothesisClass, "looks as follows"]
    let b = beta
        i = "i"
        j = "j"
        n = "n"
    ma $ setcmpr (hyp_ !: b) (b ∈ reals ^ (p + 1))
         <> quad <> text "where" <> quad <>
         pred x =: b !: 0 + sumcmpr (j =: 1) p (x !: j * b !: j)
         =: trans x /.\ b

    de $ do
        s ["Using the", quadraticLoss, function, "we define a", costFunction, "called the", residualSumOfSquares', "as the sum of all the losses"]
        s ["Concretely that looks as follows for ", m n, " ", dataPoints]
        ma $ rss b === sumcmpr (i =: 1) n ((pars $ (y !: i) - trans (x !: i) /.\ b) ^ 2)
    let xs = "X"
        ys = "Y"
    s ["If we put all the datapoints in a ", m $ n `times` (pars $ p + 1), matrix, m xs, "and all the labels in a", vector, m ys, ", then this can be written as follows"]
    ma $ rss b =: trans (pars $ ys - xs /.\ b) /.\ (pars $ ys - xs /.\ b)

    leastSquaresP
    ridgeRegressionP
    lassoRegressionP
    generalRidgeRegressionP


leastSquaresP :: Note
leastSquaresP = paragraph "Least squares" $ do
    let b = beta
    let xs = "X"
        ys = "Y"
    s ["The so-called method of least squares consists of building a model ", m b, " that minimizes ", m $ rss b]
    thm $ do
        s ["The value of", m b, " that minimizes", m $ rss b, "can be described as follows as long as", m $ trans xs /.\ xs, is, invertible]
        ma $ pest b =: (matinv $ pars $ trans xs /.\ xs) /.\ (trans xs) /.\ ys
        proof $ do
            let b = beta
                i = "i"
                j = "j"
                k = "k"
                n = "n"
                p = "p"
                x = "x"
                y = "y"
            s ["Differentiating the equation for ", m $ rss b, " with respect to ", m $ b !: j, " gives us the following"]
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
        ysp = ys <> "'"
    s ["The entire prediction", m ysp, "for a given", matrix, m xsp, "of", inputFeatures, "is computed as follows"]
    ma $ ysp =: xsp /.\ hat b

    thm $ do
        let a = alpha
        s [m $ pest b, " is an", unbiased_, pointEstimator, "of", m a]
        proof $ do
            aligneqs
                (bs a $ pest b)
                [
                    ev (pest b) - a
                  , ev ((matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ ys) - a
                  , ev ((matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ (pars $ xs /.\ alpha + nois_)) - a
                  , ev ((matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ xs /.\ alpha
                       + (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_) - a
                  , ev (alpha + (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_) - a
                  , ev alpha + ev ((matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ nois_) - a
                  , alpha + (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ ev nois_ - a
                  , alpha + (matinv $ pars $ trans xs /.\ xs) /.\ trans xs /.\ 0 - a
                  , alpha - a
                  , 0
                ]
            refs [
                expectationOfConstantTheoremLabel
              , linearityOfExpectationTheoremLabel
              ]
            s ["Note that all but", m nois_, "is constant in the above derivation and that we use the assumption that the", expectedValue, "of the", noise, "is", m 0]

    thm $ do
        let p = "p"
        ma $ (var $ pest b) =: (var_) * (matinv $ pars $ trans xs /.\ xs)
        proof $ do
            aligneqs
                (var $ pest b)
                [
                  ev ((pest b) ^ 2) - (ev (pest b)) ^ 2
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
                  (var_) * id (p + 1)
                  /.\ xs /.\ trans (matinv $ pars $ trans xs /.\ xs)
                , (var_) *
                  cancel (matinv $ pars $ trans xs /.\ xs)
                  /.\ cancel (pars $ trans xs /.\ xs)
                  /.\ trans (matinv $ pars $ trans xs /.\ xs)
                , (var_) * trans (matinv $ pars $ trans xs /.\ xs)
                , (var_) * (matinv $ pars $ trans xs /.\ xs)
                ]
            refs [
                expectationOfConstantTheoremLabel
              , linearityOfExpectationTheoremLabel
              , varianceInTermsOfExpectationTheoremLabel
              , matrixTimesTransposeIsSymmetricTheoremLabel
              , inverseOfSymmetricMatrixIsSymmetricTheoremLabel
              ]
            s ["Here we used", m $ ev (nois_ /.\ trans nois_) =: var_ * id (p + 1)]
            aligneqs
                (ev $ nois_ /.\ trans nois_)
                [
                    var nois_ + (ev nois_)^2
                  , sigma ^ 2 * id_
                ]

            s ["In the last step we used that, because the coordinates of ", m nois_, "are", independent, ", the", covariance, "of", "any two coordinates of the", noise, vector, "is zero, if they are different coordinates and one otherwise"]
    thm $ do
        textbf "Optimality of the least squares estimate"
        newline
        s ["The least squares estimate of the ", parameter, m b, "has the smallest", variance, "among all linear unbiased estimates"]
        toprove

    s ["If", m $ trans xs /.\ xs, "is not", invertible, ", for example when some", dataPoints, "are linearly dependent, then", m $ matinv $ pars $ trans xs /.\ xs, "does not exist"]
    s ["If we use the ", pseudoInverse, "instead of the", inverse, "we risk overfitting"]
    s ["The symptoms of this problem are very large coordinates in", m b]

ridgeRegressionP :: Note
ridgeRegressionP = paragraph "Ridge Regression" $ do
    s [ridgeRegression', ", like the least squares method, also minimizes a", costFunction]
    let b = beta
        p = "p"
        xs = "X"
        ys = "Y"
    de $ do
        s ["Let", m xs, "be a", matrix, "of", inputFeatures, and, m ys, "a", matrix, "of labels"]
        s [the, ridgeCost', "is a", costFunction, "defined as follows with a", parameter, m lambda]
        let j = "j"
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
        ma $ pest b =: (matinv $ pars $ trans xs /.\ xs + lambda * id (p + 1)) /.\ (trans xs) /.\ ys
        toprove

    let w = matinv $ pars $ trans xs /.\ xs + lambda /.\ id (p + 1)
    thm $ do
        s [the, bias, "of", m $ pest b, "in", ridgeRegression]
        ma $ bs alpha (pest b) =: - lambda * w /.\ b
        toprove

    thm $ do
        s [the, variance, "of", m $ pest b, "in", ridgeRegression]
        ma $ var (pest b) =: var_ * w /.\ trans xs /.\ xs /.\ w
        toprove
    -- SVD of ridge regression solution


lassoRegressionP :: Note
lassoRegressionP = paragraph "LASSO Regression" $ do
    s ["Least absolute shrinkage and selector operator (LASSO) regression, like the other methods above, also minimizes a cost function"]
    de $ do
        let xs = "X"
            ys = "Y"
        s ["Let", m xs, "be a", matrix, "of", inputFeatures, and, m ys, "a", matrix, "of labels"]
        s [the, lASSOCost', "is a", costFunction, "defined as follows with a", parameter, m lambda]
        let b = beta
            j = "j"
            p = "p"
        ma $ ridge b lambda ===
             rss b
             +
             lambda * sumcmpr (j =: 1) p (abs $ b !: j)


generalRidgeRegressionP :: Note
generalRidgeRegressionP = paragraph "Generalized Ridge Regression" $ do
    let q = "q"
    s ["Ridge regression can be generalized to have a shrinkage term parametrized by", m q]
    de $ do
        s ["The generalized", ridgeCost, "is a", costFunction, "with", parameter, m q]
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
    s ["Given a nonlinear transformation", m $ fun f (reals ^ p) reals, the, hypothesisClass, "of", the, nonlinearRegression, "method is the following set"]
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
        ma $ pest theta =: argmax theta (cprob x theta)

bayesianLearningSS :: Note
bayesianLearningSS = do
    todo "bayesian learning"
