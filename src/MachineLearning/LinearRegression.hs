module MachineLearning.LinearRegression (
    linearRegression
  ) where

import           Notes

linearRegression :: Notes
linearRegression = notesPart "linear-regression" body

body :: Note
body = do
  intro
  linearModelAndLeastSquares

x = "X"
y = "Y"

intro :: Note
intro = do
  subsection "Regression"

  s ["Regression is a supervised learning technique"]
  s ["It assumes that the input space is ", m (realVecSpace "p"), " and the output space is ", m reals]

  s ["It also assumes that the input ", m x, " the output ", m y, " the parameters of the model ", m theta, " and the noise on the observations ", m mlnv, " can be modelled as random variables"]
  ma $ y =: mlm `fn` (cs [mlmp, x]) + mlnv

  -- Parametric Statistics: the functional form of the likelihood
  -- P(X, Y|θ) is given; we want to estimate the parameters θ of the likelihood.
  -- Non-Parametric Statistics: we sample X, Y to estimate the likelihood.
  -- Statistical Learning Theory: we minimize the empirical risk directly without estimating the likelihood.
  --
  -- prior: P(model)
  -- likelihood: P(data|model)
  -- posterior: P(model|data)
  -- evidence: P(data)

linearModelAndLeastSquares :: Note
linearModelAndLeastSquares = do
  subsection "Linear Model and Least Squares"
  s ["Let a data point be a ", m p, "-dimensional vector of real numbers and let the output be a real number"]
  s ["Given a vector of inputs ", m (trans x =: (veclist (x_ 1) (x_ 2) (x_ p))), ", we predict the output ", m y, " via the following model"]
  ma $ hat y =: b_ 0 + sumcmpr (j =: 1) p (x_ j * b_ j)
  s ["Here, ", m (b_ 0), " is called the ", term "intercept", or, term "bia"]
  s ["To make equations easier, we often increase the size of the input vector by one by adding a constant ", m 1, " in the zeroeth spot and representing the ", m (b_ j), " in a vector ", m (trans (hat beta) =: veclist (b_ 0) (b_ 1) (b_ p))]
  s ["The linear model is then written in vector form as an inner product:"]
  ma $ hat y =: trans x * hat beta


  s ["To fit the linear model to a set of training data, we pick the coefficients ", m (hat beta), " sich that the ", term "residual sum of squares", " ", term "(RSS)", " is minimized"]
  s ["This is called the method of ", term "least square"]
  ma $ "RSS" `funapp` beta =: sumcmpr (i =: 1) n ((pars (("y" !: i - trans ("x" !: i) * beta))) ^: 2) =: (trans . pars $ y - x * beta) * (pars $ y - x * beta)

  s ["Differentiating with respect to ", m beta, ", we get the ", term "normal equation"]
  ma $ (trans x) * (pars $ "y" - x * beta) =: 0

  s ["If ", m ((trans x) * x), " is invertible, then the unique solution is given by the folowing equation:"]
  ma $ hat beta =: (matinv . pars $ (trans x) * x) * (trans x) * y

  s ["The fitted value for input ", m ("x" !: i), " is then ", m ((hat $ "y" !: i) =: (trans "x" !: i) * hat beta), " and the prediction for an arbitrary input ", m "x", " would be ", m ((hat "y" `funapp` "x" !: 0) =: (trans "x") * hat beta)]

  s ["Viewed as a function over the ", m p, "-dimensional input space, the ideal model: ", m f, " is linear"]
  ma $ func f (reals ^: p) reals x (trans x * beta)

  where
    b_ n = hat beta !: n
    n = "N"
    f = "f"
    i = "i"
    j = "j"
    p = "p"
    x = "X"
    x_ n = x !: n
    y = "Y"






