module MachineLearning.Main (machineLearning) where

import           Notes

machineLearning :: Notes
machineLearning = notes "machine-learning" $
  [
      notesPart "header" (chapter "Machine Learning")
    , notesPart "supervised-learning" supervisedLearning
  ]

supervisedLearning :: Note
supervisedLearning = do
  section "Supervised Learning"
  learningProblem
  taxonomyOfData
  scales
  linearModelAndLeastSquares

learningProblem :: Note
learningProblem = do
  subsection "The learning problem"
  s ["Given a set of data points in an input space ", m x, ", all tagged with a value in a certain output space ", m y, ", we search a function ", m (fun f x y), " that accurately predicts the output feature corresponding to the input value of new data points"]
  newline
  s [dquoted "Inputs", " is what they are called in machine learning"]
  s ["In statistical literature they are ofter called ", term "predictors"]
  s ["In pattern recognition, these are called ", term "feature"]
  s [dquoted "Outputs", " are called ", term "dependent variables", " in statistics and ", term "responses", " in pattern recognition"]
  where
    x = "X"
    y = "Y"
    f = "f"
    l = "l" !: f

-- Conditional expected risk
-- total expected risk
-- emperical risk
-- training data
-- test data
-- validation data
-- emperical test error
-- expected risk


-- NIY
lossfunctions :: Note
lossfunctions = do
  s ["The quality of the estimation is assessed using a ", term "loss function", " ", m (fun l x realsp ), " that measures the difference between the actual output for a given data point and the predicted output"]

  "Examples of loss functions: "
  itemize $ do
    item $ do
      term "quadratic loss"
      " (regression): "
      m $ l `funapp` "x" =: (pars $ ("y" `funapp` "x" - f `funapp` "x")) ^: 2
    item $ do
      term "0-1 loss"
      " (classification): "
      m $ l `funapp` "x" =: mathbb "I" !: ("y" ≠ "x")
    item $ do
      term "exponential loss"
      " (classification): "
      m $ l `funapp` "x" =: exp (- beta * y * (funapp f "x"))
      " for some "
      m beta
  where
    x = "X"
    y = "Y"
    f = "f"
    l = "l" !: f

-- NIY
variableTypes :: Note
variableTypes = do
  subsection "Variable Types"

  "quantitative"
  " vs "
  "quantitative"

taxonomyOfData :: Note
taxonomyOfData = do
  subsection "Taxonomy of data"
  s ["We are given an object space ", m mlos]
  s ["A ", term "measurement", " is a partial function from the object space to a ", term "domain", " ", m mldom]
  s ["This measurement is used to gather data about the objects"]
  s ["Ideally the domain has some more convenient mathematical properties than the raw object spae"]

  s ["A carthesian product of object spaces can be an object space in itself"]
  s ["A single object space is called ", term "monadic"]
  s ["A carthesian product of two object spaces is called ", term "diadic"]
  s ["A carthesian product of multiple object spaces is called ", term "polyadic"]

  ex $ do
    s ["Let the object space be the set of all possible positions on the earth"]
    s ["The measurement could map a position into the temperature at that position"]
    ma $ fun mlmes mlos reals
  ex $ do
    s ["Let the object space be the carthesian product of the set of all websites ", m (mlos !: 1), and, " the set of all words ", m (mlos !: 2)]
    s ["The measurement could be the amount of occurences of that word on that website"]
    ma $ fun mlmes (mlos !: 1 ⨯ mlos !: 2) naturals
  ex $ do
    s ["In preferential choice analysis, the object space is often the carthesian product of the set of test persons ", m (mlos !: 1), " with the set of choices ", m (mlos !: 2), " twice"]
    s ["The measurement then maps this space into a boolean choice"]
    ma $ fun mlmes (mlos !: 1 ⨯ mlos !: 2 ⨯ mlos !: 2) (setofs ["left", "right"])

scales :: Note
scales = do
  subsection "Scales"

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







