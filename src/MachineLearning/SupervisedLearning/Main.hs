module MachineLearning.SupervisedLearning.Main where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Distances.Terms
import           Logic.FirstOrderLogic.Macro

import           MachineLearning.SupervisedLearning.Regression
import           MachineLearning.SupervisedLearning.SupportVectorMachines

import           MachineLearning.SupervisedLearning.Macro
import           MachineLearning.SupervisedLearning.Terms

supervisedLearningS :: Note
supervisedLearningS = section "Supervized learning" $ do
    taxonomyOfData
    scales
    transformationInvariances

    learningProblemSS
    trainingAndTestSets
    lossFunctionSS
    trainingErrorDefinition
    generalisationErrorDefinition

    regressionS
    supportVectorMachinesS

taxonomyOfData :: Note
taxonomyOfData = subsection "Taxonomy of data" $ do
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
scales = subsection "Scales" $ do
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
    ex $ "The Farenheit scale of temperature is an interval scale"

    de $ s [the, term "ratio scale", " describes data where the ", dquoted "zero", " is meaningful but the measurement unit does not necessarily"]
    ex $ "The Kelvin scale of temperature is a ratio scale"

    de $ s [the, term "absolute scale", " describes data where also the measurement unit carries information"]
    ex $ "The amount of questions you got right on an exam is an absolute scale"


transformationInvariances :: Note
transformationInvariances = subsection "Transformation Invariances" $ do
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
    f_ = fn f
    fs n = m (setcmpr (fun f reals reals) n)
    ln = lnbk <> hline
    x = "x"
    x1 = x !: 1
    x2 = x !: 2
    a = "a"
    c = "c"


learningProblemSS :: Note
learningProblemSS = subsection "Learning problems" $ do
    learningProblemDefinition
    learningProblemExamples

learningProblemDefinition :: Note
learningProblemDefinition = de $ do
    lab learningProblemDefinitionLabel
    lab predictorDefinitionLabel
    lab featureDefinitionLabel
    lab dependentVariableDefinitionLabel
    lab responseDefinitionLabel
    s ["Given a set of ", dataPoint, "s in an ", inputSpace, " ", m mmis_, ", all tagged with a value in a certain ", outputSpace, " ", m mmos_, ", we search a ", function, " ", m $ fun f mmis_ mmos_ , " that accurately predicts the ", outputFeature, " corresponding to the ", inputFeature, "s of new ", dataPoint, "s"]
    s ["This is called a ", learningProblem']
    s [dquoted "Inputs", " is what they are called in machine learning"]
    s ["In statistical literature they are ofter called ", predictor', "s"]
    s ["In pattern recognition, these are called ", feature', "s"]
    s [dquoted "Outputs", " are called ", dependentVariable', "s in statistics and ", response, "s in pattern recognition"]
    s ["The ", measurementSpace', " is the tuple ", m (tuple mmis_ mmos_)]
  where
    f = "f"

trainingAndTestSets :: Note
trainingAndTestSets = de $ do
    lab trainingDataDefinitionLabel
    lab testDataDefinitionLabel
    lab validationDataDefinitionLabel
    s ["To find such a ", function, ", the set of ", dataPoint, "s is split into three sets"]
    itemize $ do
        item $ trainingData'
        item $ validationData'
        item $ testData'
    s [the, trainingData, " is used to find such a ", function, ", the ", validationData, " is used to improve the process of finding that ", function, " and the ", testData, " is used to assess how good the ", function, " is at prediction"]

learningProblemExamples :: Note
learningProblemExamples = mempty

lossFunctionSS :: Note
lossFunctionSS = subsection "Loss functions" $ do
    lossFunctionDefinition
    lossFunctionExamples

lossFunctionDefinition :: Note
lossFunctionDefinition = de $ do
    s ["Given a ", learningProblem, " with ", measurementSpace, " ", m mms_, " and a prediction function ", m "f"]
    s ["A ", lossFunction', " is a ", distanceFunction_, " ", m $ fun2 lf_ mmos_ mmos_ realsp, " on the ", outputSpace]
    s ["It is used to measure how far predictions are off from the real output"]

lossFunctionExamples :: Note
lossFunctionExamples = do
    let (x, y) = ("x", "y")
    ex $ do
        s [the, quadraticLoss', " ", function]
        ma $ func2 lf_ reals reals realsp x y $ (pars $ (y - x)) ^: 2
    ex $ do
        s [the, term "0-1 loss", " ", function]
        ma $ func2 lf_ mmos_ mmos_ (ccint 0 1 ⊆ realsp) x y $ mathbb "I" !: (x ≠ y)
    ex $ do
        s [the, exponentialLoss', " ", function, " with parameter ", m beta]
        let sp = setofs [-1, 1]
        ma $ func2 lf_ sp sp realsp x y $ exp (- beta * x * y)

trainingErrorDefinition :: Note
trainingErrorDefinition = de $ do
    lab trainingErrorDefinitionLabel
    s [the, trainingError', " is the sum of the losses over the training set"]
    -- TODO define training/test set first
    -- Number of errors on training data

generalisationErrorDefinition :: Note
generalisationErrorDefinition = mempty
    -- Number of mistakes on _unknown_ test data
