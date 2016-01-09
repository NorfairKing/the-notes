module MachineLearning.SupervisedLearning.Main where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Distances.Terms
import           Logic.FirstOrderLogic.Macro
import           Relations.Domain.Terms
import           Sets.Basics.Terms
import           Sets.CarthesianProduct.Terms

import           MachineLearning.SupervisedLearning.Regression
import           MachineLearning.SupervisedLearning.SupportVectorMachines

import           MachineLearning.SupervisedLearning.Macro
import           MachineLearning.SupervisedLearning.Terms

supervisedLearningS :: Note
supervisedLearningS = section "Supervized learning" $ do
    learningProblemSS
    taxonomyOfDataSS
    scalesSS
    transformationInvariancesSS
    trainingAndTestSets
    lossFunctionSS
    errorSS

    regressionS
    supportVectorMachinesS

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
    lab hypothesisDefinitionLabel
    s ["Given a ", set, " of ", dataPoints', ", also called a ", dataset', " in an ", inputSpace', " ", m mmis_, ", all tagged with a value in a certain ", outputSpace', " ", m mmos_, ", we search a ", function, " ", m $ fun f mmis_ mmos_ , " that accurately predicts the ", outputFeature', " corresponding to the ", inputFeatures', " of new ", dataPoints]
    s ["Such a function is called a ", hypothesis']
    s [dquoted "Inputs", " is what they are called in machine learning"]
    s ["In statistical literature they are ofter called ", predictors']
    s ["In pattern recognition, these are called ", features']
    s [dquoted "Outputs", " are called ", dependentVariables', " in statistics and ", responses, " in pattern recognition"]
    s ["The ", measurementSpace', " is the tuple ", m (tuple mmis_ mmos_)]
    s ["The problem of finding a ", hypothesis, " given a ", dataset, " is called a ", learningProblem']
  where
    f = "f"

learningProblemExamples :: Note
learningProblemExamples = mempty


taxonomyOfDataSS :: Note
taxonomyOfDataSS = subsection "Taxonomy of data" $ do
    s ["We are given an ", objectSpace, " ", m mlos]
    s ["A ", measurement', " is a ", function, " from the ", objectSpace, " to a ", domain, " ", m mldom]
    s ["This ", ", measurement, ", " is used to gather data about the objects"]
    s ["Ideally the domain has some more convenient mathematical properties than the raw ", objectSpace]

    s ["A ", carthesianProduct, " of ", objectSpaces, " can be an object space in itself"]
    s ["A single object space is called ", monadic']
    s ["A ", carthesianProduct, " of two ", objectSpaces, " is called ", diadic']
    s ["A ", carthesianProduct, " of multiple ", objectSpaces, " is called ", polyadic']

    ex $ do
        s ["Let the ", objectSpace, " be the set of all possible positions on the earth"]
        s ["The ", measurement, " could map a position into the temperature at that position"]
        ma $ fun mlmes mlos reals
    ex $ do
        s ["Let the ", objectSpace, " be the ", carthesianProduct, " of the ", set, " of all websites ", m (mlos !: 1), and, " the set of all words ", m (mlos !: 2)]
        s ["The ", measurement, " could be the amount of occurences of that word on that website"]
        ma $ fun mlmes (mlos !: 1 ⨯ mlos !: 2) naturals
    ex $ do
        s ["In preferential choice analysis, the ", objectSpace, " is often the ", carthesianProduct, " of the ", set, " of test persons ", m (mlos !: 1), " with the set of choices ", m (mlos !: 2), " twice"]
        s ["The ", measurement, " then maps this space into a boolean choice"]
        ma $ fun mlmes (mlos !: 1 ⨯ mlos !: 2 ⨯ mlos !: 2) (setofs ["left", "right"])


scalesSS :: Note
scalesSS = subsection "Scales" $ do
    s ["Data are of different ", scales]
    s ["This means that they have to be treated in different ways"]
    s ["Eventhough most ", measurements, " will be represented by numbers eventually, we cannot just treat them as numbers with all their properties depending on what the numbers represent"]


    de $ s [the, nominalScale', " describes qualitative measurements with a finite amount of possibilities"]
    ex $ s ["Data about presence or absence is nominal"]
    ex $ s ["The taste categories: ", dquoted "sweet, sour, salty, bitter", " are nominal"]

    de $ do
        s [the, ordinalScale', " describes data that is ranked with respect to an order"]
        s ["Only the order matters however, not the absolute values or the difference between values."]
    ex $ do
        s ["Typically self-assesment questions are on an ordinal scale"]
        s ["These may be questions like ", dquoted "How happy are you?", " where you have to tick one of three boxes: ", cs [dquoted "A. Unhappy", dquoted "B. OK", dquoted "C. Happy"]]

    de $ s [the, intervalScale', " describes data where the difference between datapoints carries information"]
    ex $ "The Farenheit scale of temperature is an interval scale"

    de $ s [the, ratioScale', " describes data where the ", dquoted "zero", " is meaningful but the ", measurement, " unit does not necessarily"]
    ex $ "The Kelvin scale of temperature is a ratio scale"

    de $ s [the, absoluteScale', " describes data where also the ", measurement, " unit carries information"]
    ex $ s ["The amount of questions you got right on an exam is an absolute scale"]
    nte $ s ["That doesn't mean it should be used as an absolute measure of conpetence"]



transformationInvariancesSS :: Note
transformationInvariancesSS = subsection "Transformation Invariances" $ do
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



trainingAndTestSets :: Note
trainingAndTestSets = de $ do
    lab trainingDataDefinitionLabel
    lab testDataDefinitionLabel
    lab validationDataDefinitionLabel
    s ["To find such a ", function, ", the ", dataset, " ", m ds_, " is usually split into three ", sets]
    itemize $ do
        item $ trainingData'   <> " " <> m trds_
        item $ validationData' <> " " <> m vds_
        item $ testData'       <> " " <> m tds_
    ma $ ds_ =: trds_ ∪ vds_ ∪ tds_
    s [the, trainingData, " is used to find such a ", function, ", the ", validationData, " is used to improve the process of finding that ", function, " and the ", testData, " is used to assess how good the ", function, " is at prediction"]

lossFunctionSS :: Note
lossFunctionSS = subsection "Loss functions" $ do
    lossFunctionDefinition
    lossFunctionExamples

lossFunctionDefinition :: Note
lossFunctionDefinition = de $ do
    s ["Given a ", learningProblem, " with ", measurementSpace, " ", m mms_, " and a ", hypothesis, " ", m "f"]
    s ["A ", lossFunction', " is a ", distanceFunction_, " on the ", outputSpace]
    ma $ fun2 lf_ mmos_ mmos_ realsp
    s ["It is used to measure how far predictions are off from the real output"]
    newline
    let f = "f"
    s ["Often, given a ", function, " ", m $ fun f mmis_ mmos_, ", ",  m $ lf_ !: f, " is used to denote the difference between the actual label of a given ", dataPoint, " ", m "x", " and the predicted label"]

lossFunctionExamples :: Note
lossFunctionExamples = do
    let (x, y) = ("x", "y")
    ex $ do
        s [the, quadraticLoss', " ", function]
        ma $ func2 lf_ reals reals realsp x y $ (pars $ (y - x)) ^: 2
    ex $ do
        s [the, term "0-1 loss", " ", function, " is ", m 1, " whenever the arguments differ and ", m 0, " otherwise"]
        ma $ func2 lf_ mmos_ mmos_ (ccint 0 1 ⊆ realsp) x y $ mathbb "I" !: (x ≠ y)
    ex $ do
        s [the, exponentialLoss', " ", function, " with parameter ", m beta]
        let sp = setofs [-1, 1]
        ma $ func2 lf_ sp sp realsp x y $ exp (- beta * x * y)

errorSS :: Note
errorSS = do
    trainingErrorDefinition
    generalisationErrorDefinition

trainingErrorDefinition :: Note
trainingErrorDefinition = de $ do
    lab trainingErrorDefinitionLabel
    s ["Given a ", learningProblem, " with ", measurementSpace, " ", m mms_, ", ", dataset, " ", m ds_, ", a ", lossFunction, " ", m lf_, " and a ", hypothesis, " ", m hyp_]
    s [the, trainingError', " is the ", mean, " of the losses over the ", trainingData]
    ma $ do
        let (x, y) = ("x", "y")
        (1 /: setsize trds_) * sumcmp (tuple x y ∈ trds_) (loss (pred x) y)

generalisationErrorDefinition :: Note
generalisationErrorDefinition = de $ do
    lab trainingErrorDefinitionLabel
    s ["Given a ", learningProblem, " with ", measurementSpace, " ", m mms_, ", ", dataset, " ", m ds_, ", a ", lossFunction, " ", m lf_, " and a ", hypothesis, " ", m hyp_]
    s [the, trainingError', " is the ", mean, " of the losses over the ", testData]
    ma $ do
        let (x, y) = ("x", "y")
        (1 /: setsize tds_) * sumcmp (tuple x y ∈ tds_) (loss (pred x) y)

