module DataMining.LargeScaleLearning where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Distances.Macro
import           Functions.Distances.Terms
import           Geometry.AffineSpaces.Macro
import           Geometry.AffineSpaces.Terms
import           Logic.PropositionalLogic.Macro
import           MachineLearning.SupervisedLearning.Macro
import           MachineLearning.SupervisedLearning.SupportVectorMachines.Terms
import           MachineLearning.SupervisedLearning.Terms
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms
import           Sets.Basics.Terms

import           DataMining.LargeScaleLearning.Macro
import           DataMining.LargeScaleLearning.Terms

largeScaleLearningS :: Note
largeScaleLearningS = section "Large scale learning" $ do
    onlineConvexProgrammingSS
    onlineConvexSupportVectorMachines

onlineConvexProgrammingSS :: Note
onlineConvexProgrammingSS = subsection "Online convex programming" $ do
    convexProgrammingProblemDefinition
    regretDefinition
    onlineConvexProgrammingProblemDefinition
    greedyProjectionSS

convexProgrammingProblemDefinition :: Note
convexProgrammingProblemDefinition = de $ do
    lab convexProgrammingProblemDefinitionLabel
    let xs = mathcal "X"
        c = "c"
        d = "d"
    s ["Let", m xs, "be a", convexSet_, "and a", subset, "of", m $ reals ^ d, "and let", m $ fun c xs realsp, "be a", convexFunction_]
    s ["The solution to a", convexProgrammingProblem', "consist of finding the element in", m xs, "that minimizes", m c]

regretDefinition :: Note
regretDefinition = de $ do
    lab regretDefinitionLabel
    lab optimalFeasableFixedPointDefinitionLabel
    lab averageRegretDefinitionLabel
    lab noRegretDefinitionLabel
    let xs = mathcal "X"
        c = "c"
        d = "d"
        t = "t"
        x = "x"
        n = "n"
    s ["Let", m xs, "be a", convexSet, "and a", subset, "of", m $ reals ^ d, "and let", m $ sequ c t, "be a", sequence, "of", convexFunctions]
    s ["Let", m $ sequ x t, "be a", sequence, "of points in", m xs]
    s [the, regret', "of", m $ sequ x t, "until round", m n, "is defined as follows"]
    ma $ reg n === pars (sumcmpr (t =: 1) n (fn (c !: t) (x !: t))) - opt n
    s ["Here, ", m $ opt n, "is the cost of the so-called", optimalFeasableFixedPoint']
    ma $ opt n === min (x ∈ xs) (sumcmpr (t =: 1) n (fn (c !: t) x))
    s [the, averageRegret', "is defined as follows"]
    ma $ areg n === (reg n /: n)
    s [m $ sequ x t, "is said to have", noRegret', "if the following holds for any", sequence, "of cost functons", m $ sequ c t]
    ma $ lim n pinfty (areg n) =: 0


onlineConvexProgrammingProblemDefinition :: Note
onlineConvexProgrammingProblemDefinition = de $ do
    lab onlineConvexProgrammingProblemDefinitionLabel
    let xs = mathcal "X"
        c = "c"
        d = "d"
        t = "t"
        x = "x"
    s ["Let", m xs, "be a", convexSet, "and a", subset, "of", m $ reals ^ d, "and let", m $ sequ c t, "be a", sequence, "of", convexFunctions]
    s ["A", onlineConvexProgrammingProblem', "consists of, for each", m t, "sequentially, picking a point", m $ x ∈ xs, "that, ideally,  minimizes", m $ reg t]

greedyProjectionSS :: Note
greedyProjectionSS = subsubsection "Greedy projection" $ do
    let xs = mathcal "X"
        c = "c"
        t = "t"
        e = eta
    de $ do
        s [the, greedyProjection', algorithm, "is an", algorithm, "to solve a general", onlineConvexProgrammingProblem]
        s ["It starts by choosing an arbitrary feasable point"]
        let x = vec "x"
            x1 = x !: 1
        ma $ x1 ∈ xs
        s ["It also chooses a", sequence, "of", learningRates, m $ sequ e t, "in", m realsp]
        s ["In round", m t, "after acquiring a cost function, it chooses the next point", m $ x !: (t + 1), "as follows"]
        ma $ x !: (t + 1) =: proj xs ((x !: t) - (eta !: t) * fn (grad (c !: t)) (x !: t))
        s ["In this projection, we use the euclidean norm", "as a", metric]

    thm $ do
        let n = "n"
            d = "D"
            g = "G"
            x = "x"
            y = "y"
        s [the, "following holds for the", greedyProjection', algorithm, "if", m $ e !: t =: (1 /: sqrt t)]
        ma $ reg n <= ((d ^ 2 * sqrt n) /: 2) + g ^ 2 * pars (sqrt n - (1 /: 2))
        "where"
        ma $   d =: max (cs [x, y] ∈ xs) (norm $ x - y)
            <> text " and "
            <> g =: max (cs [x ∈ xs, t ∈ setlst 1 n]) (norm $ grad $ fn (c !: t) x)
        toprove -- http://courses.cms.caltech.edu/cs253/slides/cs253-lec3-convex.pdf

onlineConvexSupportVectorMachines :: Note
onlineConvexSupportVectorMachines = subsection "Online convex programming for support vector machines" $ do
    let w = vec "w"
        t = "t"
        n = "n"
        i = "i"
        d = "d"
        e = eta
        yi = "y" !: i
        xi = vec "x" !: i
        ws = mathcal "W"
    s ["Recall the following", supportVectorMachines, "optimization formulation"]
    ma $ min w (sumcmpr (t =: 1) n (maxof $ setofs [0, 1 - yi * w /.\ xi])) <> text " such that " <> w /.\ w <= (1 /: lambda)

    s ["Viewed as a", onlineConvexProgrammingProblem, ", the feasable set is the following"]
    ma $ ws =: setcmpr (w ∈ reals ^ d) (w /.\ w <= (1 /: lambda))

    s ["Projection on to the feasable set is the following function"]
    ma $ func ("Proj" !: ws) (reals ^ d) ws w $ (1 /: (sqrt lambda * norm w)) * w
    s ["Note that this function is very efficiently computable"]

    s [the, learningRate, "in each round is the confidence in the prediction"]


    s ["All that's left to complete the description of an", onlineConvexProgrammingProblem, "is the", gradient, "of the cost functions"]
    s ["The problem is that the", hingeLoss, function, "is not differentiable for", m $ yi * w /.\ xi =: 1]
    s ["Luckily, any", subgradient, "will do"]
    todo "define subgradient" -- https://en.wikipedia.org/wiki/Subderivative

    let a = "a"
    s ["The set of", subgradients, "of the", hingeLoss, function, ", given an example", m $ tuple xi yi, "is the", set, "of all", functions, "as follows with", m $ a ∈ ccint 0 1]
    ma $ cases $ do
        0           & text " if " <> yi * w /.\ xi >  1
        lnbk
        a           & text " if " <> yi * w /.\ xi =: 1
        lnbk
        (- yi * xi) & text " if " <> yi * w /.\ xi <  1
        lnbk

    todo "full algorithm here, in algorithm style"
    s [the, greedyProjection, algorithm, "for", supportVectorMachines, "then looks as follows"]

    hereFigure $ renderAlgorithm $ do
        w !: 0 <-. vec 0
        lnbk
        i <-. 0
        lnbk
        whileS true $ do
            i <-. i + 1
            lnbk
            let wi = w !: i
                ei = e !: i
            ifElseS (yi * wi /.\ xi >= 1)
                (wi <-. w !: (i - 1)) $ do
                    let w' = w <> "'"
                    w' <-. w !: (i - 1) + ei * yi /.\ xi
                    lnbk
                    wi <-. w' * minof (setofs [1, (1 /: (sqrt lambda * norm w'))])

        caption "OCP SVM"


    s ["This concept can also be used to train", supportVectorMachines, "with batches of data"]
    s [the, supportVectorMachines, "are still trained point by point, but now the", algorithm, "will output the following vector after every batch of", m n, "examples"]
    ma $ w =: (1 /: n) * sumcmpr (t =: 1) n (w !: t)

    thm $ do
        let l = fn "L"
        s ["Define", m $ l w =: ev (hinge xi yi !: w), "to be the", expectedValue, "of the loss over the seen examples of the final vector"]
        ma $ ev (l w) <= l (w ^: "*") + areg n
        s ["Here, the left part of the equation is the", expectedValue, "of the loss due to the final vector accross the entire", dataset]

        clarify "what is this w star?"

