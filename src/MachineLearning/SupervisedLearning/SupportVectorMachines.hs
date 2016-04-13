module MachineLearning.SupervisedLearning.SupportVectorMachines where

import           Notes                                                          as N

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Distances.Macro
import           Geometry.AffineSpaces.Terms
import           LinearAlgebra.VectorSpaces.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro

import           MachineLearning.SupervisedLearning.Macro
import           MachineLearning.SupervisedLearning.Terms

import           MachineLearning.SupervisedLearning.SupportVectorMachines.Macro
import           MachineLearning.SupervisedLearning.SupportVectorMachines.Terms

supportVectorMachinesS :: Note
supportVectorMachinesS = subsection "Support vector machines" $ do
    svmContext
    hardConstraintsSVM
    softConstraintsSVM
    naturalForm
    computingMargin

    preferentialChoiceExample
    asymSVM


gradientDescentS :: Note
gradientDescentS = subsection "Gradient descent" $ do
    regularGradientDescentSS
    stochasticGradientDescentSS

regularGradientDescentSS :: Note
regularGradientDescentSS = do
    let ff = "F"
        f = fn ff
        (a, b) = ("a", "b")
    de $ do
        lab gradientDescentDefinitionLabel
        s ["Given a multi-variable", function, m ff, " that is everywhere ", differentiable, "with a continuous", derivative, " we can find a ", localMinimum, " (and analogously a ", localMaximum, ") using the gradient of that", function, ", starting at a point ", m a]
        newline
        s ["The first insight is that, at a point ", m a, ", ", m ff, " decreases fastest when going in the direction of the negative gradient of ", m ff, " at ", m a]
        let grf = fn $ grad ff
        s ["This means that, for ", m gamma, " small enough, ", m $ f a >= f b, " holds where ", m $ b =: a - gamma * grf a]
        s ["Repeating this step gets us a sequence of points with a decreasing value under ", m ff]
        s [m gamma, " is called the ", defineTerm "step size", " and it can change every step"]
        s ["If ", m gamma, " is small enough in each step, this means that the sequence of poince will converge to a local minimum"]
        newline
        s ["This process is called ", gradientDescent']

    nte $ s ["It is of course imperative that the gradient can be computed (efficiently)"]
    todo "This is very much a first draft of this section. It should be moved to a better place as this is not machine learning but ... optimisation?"
    todo "define a gradient"
    todo $ s ["flesh out what the exact requirements are on ", m ff, and, m gamma, " so that this process actually gets us a, ", localMinimum]
    nte $ s ["The ", localMaximum, " can analogously be obtained by going in the direction of the positive gradient"]

stochasticGradientDescentSS :: Note
stochasticGradientDescentSS = subsubsection "Stochastic gradient descent" $ do
    let ff = "F"
    de $ do
        s ["When the ", function, " to minimize can be written as the sum of ", differentiable, functions, ", the process of ", gradientDescent, " can be sped up by adding an element of randomness"]
        s ["Instead of taking the gradient of the entire ", function, m ff, ", we instead take the gradient of just one defineTerm of the sum that comprises ", m ff, " and take a step in the opposite direction"]
        s ["This process is called ", stochasticGradientDescent']
    todo "This is also a first draft, the real deal is much more complicated"


normalVector :: Note
normalVector = ix "normal vector"

svmContext :: Note
svmContext = note "context" $ do
    lab supportVectorMachinesDefinitionLabel
    s [supportVectorMachines', " are ", supervisedLearning, " models with associated learning algorithms that are trained to perform binary classification"]

hardConstraintsSVM :: Note
hardConstraintsSVM = subsubsection "SVM with hard constraints" $ do
    let (b, p, w, x, y) = ("b", vec "p", vec "w", vec "x", "y")
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
        s [the, confidence', " ", m conf_, " in the prediction ", m $ y =: sign (w /.\ x + b), " of the label of a data point ", m x, " given a ", normalVector, " ", m w, " is defined as follows"]
        ma $ conf_ =: (pars $ (w /: norm w) /.\ x + b) * y
    nte $ do
        s ["Note that if ", m w, " was not normalized in this definition, we could increase the margine arbitrarily by scaling ", m w]

    s ["The problem of finding the maximum-margin ", hyperplane, " can now be rewritten as follows"]
    ma $ do
        let i = "i"
        conf_ =: (max w $ min i $ conf_ !: i)

    s ["The margin is the greatest minimal confidence and is also written as ", m conf_]

    newline

    s ["An important insight is that the maximum-margin hyperplane is entirely defined by a few closest points (one more than the dimension of the vector, if there are no degeneracies)"]
    s ["These points are called ", defineTerm "support vector", "s and they satisfy the following equation"]
    ma $ w /.\ x + b =: pm 1

    s ["As it turns out, these support vectors allow us to rewrite the problem of maximizing the margin"]
    let (x1, x2) = (x !: 1, x !: 2)
    s ["Let ", m x1, and, m x2, " be support vectors on either side of the ", hyperplane]
    align_
        [
          x2 + 2 * conf_ * (w /: norm w) & "" =: x1
        , w /.\ x1 + b & "" =:  1
        , w /.\ x2 + b & "" =: -1
        ]

    s ["Solving this system of equations for ", m conf_, " shows that ", m conf_, " is in fact the inverse of the length of ", m w]
    ma $ conf_ =: 1 /: norm w
    proof $ do
        align_
            [
              w /.\ x1 + b & "" =:  1
            , w /.\ (pars $ x2 + 2 * conf_ * (w /: norm w)) + b & "" =:  1
            , w /.\ x2 + b + 2 * conf_ * ((w /.\ w) /: norm w) & "" =: 1
            , norm w /: (w /.\ w) & "" =: conf_
            ]

    s ["This means that maximising the margin ", m conf_, " is equivalent to minimizing ", m $ norm w, " or equivalently ", m $ w /.\ w]
    s ["Now the rewritten optimisation problem looks as follows"]
    align_ $
        let i = "i" in
        [
          "" & (min w $ w /.\ w)
        , text "such that " & (fa i $ y !: i * (pars $ w /.\ x !: i + b) >= 1)
        ]
    s ["This problem is called ", defineTerm "SVM with hard constraints"]

    nte $ do
        s ["Without loss of generality, we can assume that the desired ", hyperplane, " goes through the ", origin, " given that we use the ", ix "homogenous representation", " of vectors"]
        why


softConstraintsSVM :: Note
softConstraintsSVM = subsubsection "SVM with soft constraints" $ do
    let (b, w, x, y) = ("b", vec "w", vec "x", "y")

    s ["If the data is not ", ix "linearly separable", " then this optimisation problem is not feasable"]
    s ["It can however be adapted to account for the ", quoted "mistakes"]
    let c = "C"
    let i = "i"
    let n = "n"
    let xi = x !: i
    let yi = y !: i
    let ii = mathbb "I" !: (text "point " <> i <> text " is misclassified")
    align_ $
        [
          "" & (min w $ w /.\ w + c `cdot` sumcmpr (i =: 1) n ii)
        , text "such that " & (fa i $ yi * (pars $ w /.\ xi + b) >= 1 - ii)
        ]
    s ["Here ", m c, " is a parameter that controls the the number of mistakes that the", hyperplane, "is allowed to make"]
    s ["However, not all mistakes are of the same severity"]

    let i = "i"
        n = "n"
        xii = N.xi !: i
    s ["The margin can be used to penalize mistakes via the use of so-called ", defineTerm "slack variables", " ", m xii]
    align_ $
        let i = "i" in
        [
          "" & (min w $ w /.\ w + c * sumcmpr (i =: 1) n xii)
        , text "such that " & (fa i $ yi * (pars $ w /.\ xi + b) >= 1 - xii)
        ]
    s ["Given an optimal", m w, "we can solve for", m xii, "as follows"]
    ma $ cases $ do
        yi * (pars $ w /.\ xi + b) >= 1 ⇒ xii =: 0
        lnbk
        yi * (pars $ w /.\ xi + b) <  1 ⇒ xii =: 1 - yi * (pars $ w /.\ xi + b)
    ma $ xii =: maxof (setofs [0, 1 - (pars $ (yi) * (pars $ w /.\ xi + b) )])
    nte $ do
        lab sVMSymmetricDataNoteLabel
        s ["We assume that the number of positively labeled examples is similar to the number of negatively labeled examples"]
        s ["Otherwise we would have to penalize false positives and false negatives differently"]
    nte $ do
        s ["When we set ", m c, " to ", m pinfty, " the result will be a hyperplane that separates the hyperplane"]
        s ["When we set ", m c, " to ", m 0, " then the result will ignore the data"]

    s ["This problem is called ", defineTerm "SVM with soft constraints"]


naturalForm :: Note
naturalForm = subsubsection "SVM in natural form" $ do
    let (b, w, x, y) = ("b", vec "w", vec "x", "y")
    let c = "C"
    let i = "i"
        n = "n"
    s ["The problem can be rewritten one last time"]
    ma $ argmin (w <> ", " <> b) $ w /.\ w + c * sumcmpr (i =: 1) n (maxof (setofs [0, 1 - (pars $ (y !: i) * (pars $ w /.\ x !: i + b) )]))
    s ["This formulation is called ", defineTerm "SVM in its natural form"]

computingMargin :: Note
computingMargin = subsubsection "Computing the margin" $ do
    let (b, w) = ("b", vec "w")
    s ["Since the problem is a quadratic optimisation problem, we could just use a quadratic solver"]
    newline
    s ["We can do better, however, if we are content with an arbitrarily good approxmation"]
    s [the, objectiveFunction, "is a nicely continuous", function, "in two variables: ", m w, and, m b]
    s ["This means that we can perform gradient descent to find the minimum"]

    let ff = "f"
        f = fn2 ff
        w = vec "w"
        b = "b"
        c = "C"
        i = "i"
        j = "j"
        n = "n"
        x = vec "x"
        y = "y"
    s ["In essence, we just trying to minimize the", function, m ff, " as follows"]
    ma $ f w b =: w /.\ w + c * sumcmpr (i =: 1) n (maxof (setofs [0, 1 - (pars $ (y !: i) * (pars $ w /.\ x !: i + b) )]))
    s ["The ", m j, "th coordinate of the gradiant ", m $ grad ff, " can be computed as follows"]
    ma $ grad ff !: j
      =: partd (fn2 ff w b) (w !: j)
      =: (cases $ do
            (w !: j) & " if " <> (pars $ (y !: i) * (pars $ w /.\ x !: i + b)) >= 1
            lnbk
            (w !: j) + c * sumcmpr (i =: 1) n (pars $ - (y !: i) * (x !: (cs [i, j]))) & " otherwise"
         )

    s ["The problem with this approach is that we have to go over the entire set in each iteration step"]

    newline
    s ["For really large datasets, we can do even better in terms of time"]
    s ["Using ", stochasticGradientDescent, " we can also obtain the ", localMinimum, " by evaluating the gradient for each individual training example instead of over the entire dataset"]
    s ["For a given datapoint ", m $ x !: i, " the gradient we use will look as follows"]
    ma $ grad ff !: j
      =: (cases $ do
            (w !: j) & " if " <> (pars $ (y !: i) * (pars $ w /.\ x !: i + b)) >= 1
            lnbk
            (w !: j) + c * (pars $ - (y !: i) * (x !: (cs [i, j]))) & " otherwise"
         )



preferentialChoiceExample :: Note
preferentialChoiceExample = ex $ do
    examq eth "Data Mining" "January 2013"
    s ["In this problem, we will develop a strategy of learning to rank objects through pairwise comparisons using", supportVectorMachines]

    let n = "n"
        xs = "X"
        x = "x"
        i = "i"
        j = "j"
        d = "d"
    s ["Let there be", m n, "objects that each have a feature vector", m $ x !: i ∈ reals ^ d]
    ma $ xs =: setlist (x !: 1) (x !: 2) (x !: n)

    let w = "w"
        w' = w ^: "*"
        f_' = "f" ^: "*"
        f' = fn f_'
        (<*) = binop $ comm0 "succ"
    let xi = x !: i
        xj = x !: j
    s ["We operate under the assumtion that there is an underlying ", textbf "linear", "ranking", function, m f_', "of the following form"]
    ma $ f' x =: w' /.\ x
    s ["This", function, "ranks objects", textbf "uniquely", ", that is, for any pair of obects", m $ tuple xi xj, "it satisfies", m $ f' xi > f' xj, "if the rank of", m xi, "is higher than the rank of", m xj]
    ma $ xi <* xj === f' xi > f' xj
    s [m w', "is called the", defineTerm "optimal preference vector"]

    newline

    let h = "h"
    s ["Show that the problem of determining the optimal preference vector", m w', "can be reduced to a problem af learning a classifier", m $ fun h (reals ^ d) (setofs [-1, 1]), ", which, for any given pair of objects", m i, and, m j, "predicts whether ", m xi, "has a higher rank than", m xj]
    proof $ do
        s ["We need to find a way to label certain vectors (not necessarily the feature vectors) with either", m 1, or, m (-1), "such that, given the solution to a linear classification problem, we can figure out the optimal preference vector"]
        s ["For any pairwise comparison ", m $ xi <* xj, "we label the vector", m (xi <-> xj), "as", m 1, "and the vector", m (xj <-> xi), "as", m (-1)]

        s ["Because the underlying ranking function is linear, this means that we now have a whole bunch of plusses and minusses at both sides of a hyperplane through the origin"]
        s ["Training a linear classifier on this constructed dataset will give us a normal vector", m w]
        s ["Given enough datapoints, this normal vector will be close to linearly dependent on the real underlying optimal preference vector"]


asymSVM :: Note
asymSVM = subsubsection "Assymmetric SVM" $ do
    examq eth "Data Mining" "January 2013"

    s [supportVectorMachines, "usually assume that data is labeled symmetrically", ref sVMSymmetricDataNoteLabel, "by using the", hingeLoss, function]

    s ["Assymetric", supportVectorMachines, "are a variant of", supportVectorMachines, "in which the number of positive examples is much greater than the number of negative examples in the data"]
    s ["The goal is to design a variant with an assymetric", hingeLoss, function, "so that more weight is placed on misclassifications of negative examples"]
    let a = alpha
    s ["For a given", m $ a >= 1, "we can formulate the asymmetric", supportVectorMachines, "as the following optimization problem"]
    let w = vec "w"
        x = vec "x"
        y = "y"
        i = "i"
        n = "n"
        xi = x !: i
        yi = y !: i
    align_ $
        [
          ""                & (min w $ w /.\ w)
        , text "such that " & fa (yi =: 1)  (yi * w /.\ x >= 1)
        , ""                & fa (yi =: -1) (yi * w /.\ x >= a)
        ]

    let la_ = lf_ !: "asym" !: w
        la = fn2 la_
        c = "C"

    s ["Note that for", m $ a =: 1, "the problem reduces to the classic", supportVectorMachines]
    s ["By introducing slack variables to handle", noise, "we can reformulate the above optimisation problem into an online convex program using an assymetric", hingeLoss, function, "as follows"]
    ma $ min w $ w /.\ w + c * sumcmpr (i =: 1) n (la yi xi)

    itemize $ do
        item $ do
            s ["Derive the assymetric", hingeLoss, function, "for this assymetric variant of", supportVectorMachines]
            newline

            s ["Adding slack variables, analogously to the way we did for soft", supportVectorMachines, ", results in the following optimisation problem"]
            let n = "n"
                i = "i"
                xii = N.xi !: i
            align_ $
                [
                  ""                & (min w $ w /.\ w) + c * sumcmpr (i =: 1) n xii
                , text "such that " & fa (yi =: 1)  (yi * w /.\ x >= 1 - xii)
                , ""                & fa (yi =: -1) (yi * w /.\ x >= a - xii)
                ]
            s ["We distinguish two cases"]
            s ["For positive examples, we solve for", m xii, "as follows, just like for regular", supportVectorMachines]
            ma $ cases $ do
                yi * w /.\ xi >= 1 ⇒ xii =: 0
                lnbk
                yi * w /.\ xi <  1 ⇒ xii =: 1 - yi * w /.\ xi
            s ["For negative examples, we solve for", m xii, "as follows"]
            ma $ cases $ do
                yi * w /.\ xi >= a ⇒ xii =: 0
                lnbk
                yi * w /.\ xi <  a ⇒ xii =: a - yi * w /.\ xi

            s ["This means that the assymetric", hingeLoss, function, "looks as follows"]
            let la' = cases $ do
                        maxof (setofs [0, 1 - yi * w /.\ xi]) & text "if " <> yi =: 1
                        lnbk
                        maxof (setofs [0, a - yi * w /.\ xi]) & text "if " <> yi =: -1
            ma $ la yi xi =: la'
            s ["The resulting optimisation problem in primal form looks as follows"]
            ma $ min w $ w /.\ w + c * sumcmpr (i =: 1) n la'

        item $ do
            s ["Plot the assymmetric", hingeLoss, function, "seperately for a positive example and for a negative example as a function of the confidence ", m $ eta =: y * w /.\ x]
            newline

            s ["Just for the plot, as an example, ", m a, "has been chosen to be", m 2]

            let cap = do
                    "The assymetrix hinge loss for a datapoint, given its confidence " <> m eta <> ". "
                    "The red line is for a positive example and the blue line for a negative example."
            tikzFig cap ["scale" =- 0.5] $ axis [
                  "xlabel" =- m eta
                , "ylabel" =- m la_
                , "ymin" =- (-0.1)
                , "ymax" =- 4.1
                , "xmin" =- (-1.1)
                , "xmax" =- 3.1
                ] $ do
                addPlot ["color" =- "red",  "ultra thick", "domain" =- "-5:1"] $ "1-x"
                addPlot ["color" =- "red",  "ultra thick", "domain" =-  "1:5"] $ "0"
                addPlot ["color" =- "blue", "ultra thick", "domain" =- "-5:2"] $ "2-x"
                addPlot ["color" =- "blue", "ultra thick", "domain" =-  "2:5"] $ "0"


        item $ do
            s ["Derive the", subgradient, "of the assymetric", hingeLoss, function, "with respect to the weight vector", m w]
            newline
