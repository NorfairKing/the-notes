module MachineLearning.SupervisedLearning (
    supervisedLearning
  ) where

import           Notes

supervisedLearning :: Notes
supervisedLearning = notesPart "supervised-learning" body

body :: Note
body = do
  section "Supervised Learning"
  learningProblem
  taxonomyOfData
  scales
  transformationInvariances

learningProblem :: Note
learningProblem = do
  subsection "The learning problem"
  s ["Given a set of data points in an input space ", m x, ", all tagged with a value in a certain output space ", m y, ", we search a function ", m (fun f x y), " that accurately predicts the output feature corresponding to the input value of new data points"]
  newline
  s [dquoted "Inputs", " is what they are called in machine learning"]
  s ["In statistical literature they are ofter called ", term "predictors"]
  s ["In pattern recognition, these are called ", term "feature"]
  s [dquoted "Outputs", " are called ", term "dependent variables", " in statistics and ", term "responses", " in pattern recognition"]
  s ["The ", term "measurement space", " is the tuple ", m (tuple x y)]
  where
    x = "X"
    y = "Y"
    f = "f"
    l = "l" !: f

-- NYI
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
  s ["Data are of different scales"]
  s ["This means that they have to be treated in different ways"]
  s ["Eventhough most measurements will be represented by numbers eventually, we cannot just treat them as numbers with all their properties depending on what the numbers represent"]


  de $ s [the, term "nominal scale", " describes qualitative measurements with a finite amount of possibilities"]
  ex $ s ["Data about presence or absence is nominal"]
  ex $ s ["The taste categories: ", dquoted "sweet, sour, salty, bitter", " are nominal"]

  de $ do
    s [the, term "ordinal scale", " describes data that is ranked with respect to an order"]
    s ["Only the order matters however, not the absolute values or the difference between values."]
  ex $ do
    s ["Typically self-assesment questions are on an ordinal scale"]
    s ["These may be questions like ", dquoted "How happy are you?", " where you have to tick one of three boxes: ", cs [dquoted "A. Unhappy", dquoted "B. OK", dquoted "C. Happy"]]

  de $ s [the, term "interval scale", " describes data where the difference between datapoints carries information"]
  ex $ "The Farenheit scale of temperature"

  de $ s [the, term "ratio scale", " describes data where the ", dquoted "zero", " is meaningful but the measurement unit does not necessarily"]
  ex $ "The Kelvin scale of temperature"

  de $ s [the, term "absolute scale", " describes data where also the measurement unit carries information"]
  ex $ "The amount of questions you got right on an exam"

transformationInvariances :: Note
transformationInvariances = do
  subsection "Transformation Invariances"
  s ["Data is sometimes transformed for various reasons"]
  s ["It is important that we realise that some transformations alter the data and some don't"]
  s ["If data is not altered by a transformation ", m "t", " then that data is called ", m "t", "-invariant"]

  hereFigure $ do
    tabular Nothing [VerticalLine, LeftColumn, VerticalLine, LeftColumn, VerticalLine] $ do
      hline
      "scale type"  & "transformation invariances"
      ln
      hline
      "nominal"     & fs (f <> text " is bijective.")
      ln
      "ordinal"     & fs (fa (cs [x1, x2] ∈ reals) $ f_ x1 <: f_ x2)
      ln
      "interval"    & fs (te (cs [a ∈ realsp, c ∈ reals]) $ f_ x =: a * x + c)
      ln
      "ratio"       & fs (te (a ∈ realsp) $ f_ x =: a * x)
      ln
      "absolute"    & m (func f reals reals x (f_ x =: x))
      ln

    caption "Transformation invariances for different scales"

  where
    f = "f"
    f_ = funapp f
    fs n = m (setcmpr (fun f reals reals) n)
    ln = lnbk <> hline
    x = "x"
    x1 = x !: 1
    x2 = x !: 2
    a = "a"
    c = "c"


