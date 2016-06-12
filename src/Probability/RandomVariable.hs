module Probability.RandomVariable where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Distances.Terms
import           Functions.Inverse.Macro
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Probability.Independence.Terms
import           Probability.Intro.Macro
import           Probability.Intro.Terms
import           Probability.MeasurableSpace.Macro
import           Probability.MeasurableSpace.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.SigmaAlgebra.Terms
import           Relations.Domain.Terms
import           Sets.Basics.Terms

import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms


randomVariableS :: Note
randomVariableS = section "Random Variables" $ do
    introS
    distributionFunctionSS
    quantileFunctionSS
    copiesOfRandomVariablesSS
    typesOfRandomVariables
    momentsOfRandomVariables
    inequalitiesSS

psDec :: Note
psDec = s ["Let ", m prsp_, " be a ", probabilitySpace]

introS :: Note
introS = subsection "Intro" $ do
    randomVariableDefinition
    randomVariableInducesProbabilityMeasure
    setOfProbabilityDistributionsDefinition
    probabillisticFunctionDefinition
    tupleOfRandomVariablesTheorem
    tupleOfRandomVariablesDistributionDefinition



randomVariableDefinition :: Note
randomVariableDefinition = do
    let a = "A"
        b = "B"
    de $ do
        let aa = mathcal "A"
            bb = mathcal "B"
        s ["Let ", m $ prsp a aa prm_, " be a ", probabilitySpace, and, m $ mspace b bb, a, measurableSpace]

        s ["An", xyRv' a b, m rv_, "is a", measurableFunction_, m $ fun rv_ a b]
        s ["Often we call a", xyRv b bb, "also a", xRv b, "when we leave out the", sa, m bb, "or even just", quoted randomVariable]
    nte $ do
        s ["Usually when", m b, "is left out in", dquoted (xRv b) <> ", we mean an", xRv reals]

randomVariableInducesProbabilityMeasure :: Note
randomVariableInducesProbabilityMeasure = do
    let a = "A"
        b = "B"
    let aa = mathcal "A"
        bb = mathcal "B"
    let pp = prdis_ rv_
    de $ do
        lab probabilityDistributionDefinitionLabel
        s ["Let ", m $ prsp a aa prm_, " be a ", probabilitySpace, and, m $ mspace b bb, a, measurableSpace]
        s ["A", randomVariable, m $ fun rv_ a b, "induces a", probabilityMeasure, m pp, on, m bb, "in", m $ prsp b bb pp]
        ma $ fn pp b =: prob (inv rv_ `fn` b)
        s [m pp, "is called the", probabilityDistribution', "of", m rv_, "in", m $ prsp a aa prm_]
        toprove_ "prove that this is in fact a random variable"
    nte $ do
        s ["If we interpret ", m $ prob a, "as the probability that an event", m a, "occurs, then we can interpret", m $ fn pp b, "as the probability that", m $ b =: fn rv_ a, "occurs"]
    nte $ do
        s ["Sometimes notation is the notation (ab)used such that when we write", m $ prob (rv_ ⊆ b), "we really mean", m $ fn pp b]
    let b_ = "b"
    nte $ do
        s ["We then further abuse this notation such that when we write", m (prob (rv_ =: b_)) <> ", it really means", m $ prob (rv_ ⊆ setof b_)]
    nte $ do
        s ["In the case of an", xRv reals, "we further abuse", m $ prob (rv_ <= b_), "to mean", m $ prob (rv_ ⊆ ocint minfty b_)]

setOfProbabilityDistributionsDefinition :: Note
setOfProbabilityDistributionsDefinition = de $ do
    let y = mathcal "Y"
    s ["We use the notation", m $ prdss y, "to mean the", set, "of", probabilityDistributions, "of", xRvs y]

probabillisticFunctionDefinition :: Note
probabillisticFunctionDefinition = do
    de $ do
        lab probabilisticFunctionDefinitionLabel
        let x = "X"
            y = "Y"
        s ["Let", m x, and, m y, be, sets]
        let ff = "F"
            f = "f"
        s ["A", probabilisticFunction', m ff, "is a", randomVariable, "over the", set, "of", functions, m $ fun f x y]
    nte $ do
        s ["Sometimes the phrase", quoted probabilisticFunction, "is also used to mean", conditionalProbabilityDistribution, "but since that name was taken (eventhough it's arguably a more sensible definition), we will stick to this definition"]

tupleOfRandomVariablesTheorem :: Note
tupleOfRandomVariablesTheorem = thm $ do
    let a = mathbb "A"
        b = mathbb "B"
        c = mathbb "C"
        d = mathbb "D"
    let aa = mathcal "A"
        bb = mathcal "B"
        cc = mathcal "C"
        dd = mathcal "D"
    let pra = prm_ !: a
        prb = prm_ !: b
        prspa = prsp a aa pra
        prspb = prsp b bb prb
    s ["Let ", m prspa, and, m prspb, "be", probabilitySpaces, and, m $ mspace c cc, and, m $ mspace d dd, measurableSpaces]
    let x = "X"
        y = "Y"
    s ["Let", m $ fun x a c, and, m $ fun y b d, "be two", randomVariables]
    let t_ = rtup x y
    s ["The following", function <> ", denoted as", m t_, "is a", xyRv (c ⨯ d) (cc ⨯ dd)]
    let a_ = "a"
        b_ = "b"
    ma $ func t_ (a ⨯ b) (c ⨯ d) (tuple a_ b_) (tuple (fn x a_) (fn y b_))
    s ["This function is called a", randomVector, "if", m prspa, "equals", m prspb ]
    proof $ do
        let cs = "C"
            ds = "D"
            cd = cs <> ds
        s ["Let", m cd, "be an arbitrary element of", m $ cc ⨯ dd]
        s ["We have to prove the following"]
        ma $ preim t_ cd ∈ (aa ⨯ bb)
        s ["Because", m x, and, m y, "are both", randomVariables, "we already know the following"]
        ma $ preim x cs =: setcmpr a_ (fn x a_ ∈ cs) <> quad <> text and <> quad <> preim y ds =: setcmpr b_ (fn y b_ ∈ ds) ∈ bb
        let t = fn t_
        let ab = tuple a_ b_
        s ["Now observe.."]
        aligneqs (preim t_ cd)
            [ setcmpr ab (t ab ∈ cd)
            , setcmpr ab (fn x a_ ∈ c ∧ fn y b_ ∈ d)
            , setcmpr a_ (fn x a_ ∈ cs) ⨯ setcmpr b_ (fn y b_ ∈ ds)
            , preim x cs ⨯ preim y ds ⊆ aa ⨯ bb
            ]

tupleOfRandomVariablesDistributionDefinition :: Note
tupleOfRandomVariablesDistributionDefinition = de $ do
    let a = mathbb "A"
        b = mathbb "B"
        c = mathbb "C"
        d = mathbb "D"
    let aa = mathcal "A"
        bb = mathcal "B"
        cc = mathcal "C"
        dd = mathcal "D"
    let pra = prm_ ^: a
        prb = prm_ ^: b
        prspa = prsp a aa pra
        prspb = prsp b bb prb
    s ["Let ", m prspa, and, m prspb, "be", probabilitySpaces, and, m $ mspace c cc, and, m $ mspace d dd, measurableSpaces]
    let x = mathcal "X"
        y = mathcal "Y"
    s ["Let", m $ fun x a c, and, m $ fun y b d, "be two", randomVariables]
    let xy = rtup x y
    s [the, randomVariable, m xy, "again induces a", probabilityMeasure, m $ prdis_ xy, "on", m $ mspace (c ⨯ d) (cc ⨯ dd), ref probabilityDistributionDefinitionLabel]
    s ["In this context, we often use the following notation abuse"]
    ma $ prdis_ (x <> y) === prdis_ xy
    let xx_ = "X"
        yy_ = "Y"
    ma $ fn2 (prdis_ (x <> y)) xx_ yy_ === prdis xy (tuple xx_ yy_)
    let x_ = "x"
        y_ = "y"
    ma $ fn2 (prdis_ (x <> y)) x_ y_ === prdis xy (tuple (setof x_) (setof y_))
    let c_ = "c"
        d_ = "d"
        cd = tuple c_ d_
    ma $ prob (x =: x_ ∧ y =: y_) === prdis xy (setcmpr (cd ∈ c ⨯ d) (fn xy cd =: tuple x_ y_))



distributionFunctionSS :: Note
distributionFunctionSS = subsection "Cumulative distribution function" $ do
    cumulativeDistributionFunctionDefinition
    distributionFunctionCondition
    distributionBetweenValues
    distributionAfterValue


cumulativeDistributionFunctionDefinition :: Note
cumulativeDistributionFunctionDefinition = de $ do
    lab cumulativeDistributionFunctionDefinitionLabel
    lab cDFDefinitionLabel
    lab distributionFunctionDefinitionLabel
    lab probabilityDistributionDefinitionLabel
    psDec
    s ["Let ", m rvfunc_, " be a ", randomVariable]
    s ["The ", cumulativeDistributionFunction', " (" <> cDF' <> "),", distributionFunction', "as follows"]
    ma $ func df_ reals reals a $ prd (ocint minfty a) =: prob (setcmpr o (vrv o)) =: prob (rv_ <= a)
    s ["Sometimes the", distribution', " is also used as-is"]
  where
    a = "a"
    o = omega

distributionFunctionCondition :: Note
distributionFunctionCondition = thm $ do
    s ["Let ", m rv_, " be a random variable in ", m prbsp]
    s ["A function ", m (fun df_ reals reals), " is a ", cumulativeDistributionFunction, " if and only if it has the following three properties"]
    enumerate $ do
        item $ do
            s [m df_, " is monotonically increasing"]
            ma $ fa (cs [a, b] ∈ reals) $ (a <= b) ⇒ (prd a <= prd b)
        item $ do
            ma $ lim a minfty (prd a) =: 0
            ma $ lim a pinfty (prd a) =: 1
        item $ do
            s [m df_, " is right-continuous"]
            ma $ fa (a ∈ reals) $ rlim h 0 (prd $ a + h) =: prd a
            refneeded "right-continuous" -- Also use the proper index
    noproof

  where
    a = "a"
    b = "b"
    h = "h"

bdfDec :: Note
bdfDec = s ["Let ", m df_, " be a distribution function in ", m prbsp]

distributionBetweenValues :: Note
distributionBetweenValues = thm $ do
    bdfDec
    ma $ fa (cs [a, b] ∈ reals) $ prob (a < rv_ <= b) =: prd b - prd a

    toprove
  where
    a = "a"
    b = "b"

distributionAfterValue :: Note
distributionAfterValue = thm $ do
    bdfDec
    ma $ fa (a ∈ reals) $ prob (rv_ > a) =: 1 - prd a

    toprove
  where a = "a"

quantileFunctionSS :: Note
quantileFunctionSS = subsection "The quantile function" $ do
    quantileFunctionDefinition
    quartileDefinition
    medianDefinition

quantileFunctionDefinition :: Note
quantileFunctionDefinition = de $ do
    s ["The ", quantileFunction', for, m prbsp, " is the inverse of the ", distributionFunction, " ", m df_]
    s ["The value ", m (prq p), " is the smallest value ", m (a ∈ reals), " for which ", m (prd a >= p), " holds"] -- FIXME index smallest
  where
    a = "a"
    p = "p"

quartileDefinition :: Note
quartileDefinition = de $ do
    s ["The ", m "0.25", ", ", m "0.5", and, m "0.75", " ", quantile, " are respectively called the first, second and third ", quartile]

medianDefinition :: Note
medianDefinition = de $ do
    s ["The second ", quartile, " is called the ", median]

copiesOfRandomVariablesSS :: Note
copiesOfRandomVariablesSS = subsection "Copies of random variables" $ do
    independentCopyDefinition
    cloneDefinition
    copyVsCloneExample

independentCopyDefinition :: Note
independentCopyDefinition = de $ do
    lab independentCopyDefinitionLabel
    let x = "X"
    s ["Let", m x, "be a", randomVariable]
    let q = "q"
    s ["We denote by", m $ icop x q, the, randomVariable, "consisting of", m q, independentCopies', "of", m x]
    let x1 = x !: 1
        x2 = x !: 2
        xq = x !: q
    ma $ icop x q =: tuplelist x1 x2 xq
    s ["More precicely,", m $ list x1 x2 xq, "are", independent, "and have the same", probabilityDistribution, "as", m x]
    todo "More precise definition, see the definition of a random variable by itself"


cloneDefinition :: Note
cloneDefinition = de $ do
    lab cloneDefinitionLabel
    let x = "X"
    s ["Let", m x, "be a", randomVariable]
    let q = "q"
    s ["We denote by", m $ clon x q, the, randomVariable, "consisting of", m q, clones', "of", m x]
    ma $ clon x q =: tuplelist x x x
    todo "More precise definition, see the definition of a random variable by itself"


copyVsCloneExample :: Note
copyVsCloneExample = ex $ do
    let x = "X"
    s ["Let", m x, "be a binary", randomVariable, "with a uniform", distribution]
    let q = "q"
    s [m $ icop x q, "is the", randomVariable, "with uniform", distribution, "over", m $ setofs [0, 1] ^ q, "and", m $ clon x q, "is the", randomVariable, "which takes on the two values", m $ tuplelist 0 0 0, and, m $ tuplelist 1 1 1, "with", probability, m $ 1 /: 2]


typesOfRandomVariables :: Note
typesOfRandomVariables = subsection "Types of random variables" $ do
    discreteRandomVariables
    continuousRandomVariables

discreteRandomVariables :: Note
discreteRandomVariables = subsubsection "Discrete random variables" $ do
    discreteRandomVariableDefinition
    discreteDistributionDefinition
    discreteCumulativeDistribution
    discreteRandomVariableExamples
    statisticalDistanceDefinition
    statisticalDistanceUnamplifiable
    statisticalDistanceSubsets

discreteRandomVariableDefinition :: Note
discreteRandomVariableDefinition = de $ do
    s ["A ", randomVariable, " ", m rv_, " in a ", probabilitySpace, " ", m prsp_, " is called ", discrete', " if the ", image, " under ", m rv_, " is non-zero in just a countable number of points"] --FIXME index countable
    ma $ pi =: prob (setcmpr (omega ∈ univ_) (vrv omega =: xi)) =: prob (rv_ =: xi)

  where
    i = "i"
    xi = "x" !: i
    pi = "p" !: i

discreteDistributionDefinition :: Note
discreteDistributionDefinition = de $ do
    s ["A ", discreteDistribution', " ", m (sequ pi i), " of a ", discrete, " ", randomVariable, " ", m rv_, " in a ", probabilitySpace, " ", m prsp_, " is a ", sequence, " with the following properties"]
    enumerate $ do
        item $ m $ fa (i ∈ naturals) (pi >= 0)
        item $ m $ sumcmp i pi =: 1

  where
    i = "i"
    pi = "p" !: i

discreteCumulativeDistribution :: Note
discreteCumulativeDistribution = thm $ do
    s [the, distributionFunction, " ", m df_, " of a ", discrete, " ", randomVariable, " ", m rv_, " in a ", probabilitySpace, " ", m prsp_, " has a simpler formula"]
    ma $ prd a =: prob (rv_ <= a) =: sumcmp (xi <= a) pi

    toprove
  where
    a = "a"
    i = "i"
    xi = "x" !: i
    pi = "p" !: i

discreteRandomVariableExamples :: Note
discreteRandomVariableExamples = do
    ex $ do
        let h = "Heads"
            t = "Tails"
            p = "p"
            u = setofs [h, t]
        s ["Let", m u, "be the universe of the", stochasticExperiment, "of throwing up a flipping an unfair coin"]
        s ["Let", m $ powset u, "be a", sigmaAlgebra]
        s ["Let the following", function, m prm_, "be a", probabilityMeasure]
        ma $ fun prm_ (powset u) (ccint 0 1)
        ma $ cases $ do
            u & mapsto <> 1
            lnbk
            h & mapsto <> p
            lnbk
            t & mapsto <> (1 - p)
            lnbk
            emptyset & mapsto <> 0
        let x = "X"
        s ["If we were to bet that the coin would come up heads with a fifty units payoff, then that payoff could be modeled as a", discrete, randomVariable, m x, "in the", probabilitySpace, m prsp_, "as follows"]
        ma $ cases $ do
            fn x h =: 50
            lnbk
            fn x t =: 0

statisticalDistanceDefinition :: Note
statisticalDistanceDefinition = de $ do
    let x = "X"
        y = "Y"
        zz = mathcal "Z"
        z = "z"
    s [the, statisticalDistance', "between two", randomVariables, m x, and, m y, "over a", finite, set, m zz, "is defined as follows"]
    ma $ statd x y =: (1 / 2) * sumcmp (z ∈ zz) (abs $ prob (x =: z) - prob (y =: z))
    todo "Does Z need to be finite?"

statisticalDistanceUnamplifiable :: Note
statisticalDistanceUnamplifiable = thm $ do
    lab statisticalDistanceUnamplifiableTheoremLabel
    s ["A", probabilisticFunction, "cannot increase the", statisticalDistance, "of two", randomVariables]
    newline
    let x = mathcal "X"
        x1 = "X" !: 1
        x2 = "X" !: 2
        y = mathcal "Y"
        a_ = "A"
        a = fn a_
    s ["Let", m x1, and, m x2, be, randomVariables, over, m x]
    s ["Let", m a_, "be a", randomVariable, "over the", set, "of", functions, m $ fun "" x y, "such that", m a_, and, m x1, are, independent, and, m a_, and, m x2, are, independent]
    ma $ statd (a x1) (a x2) <= statd x1 x2

    proof $ do
        let u = "u"
            v = "v"
        aligneqs (statd (a x1) (a x2))
            [  (1 / 2) * sumcmp (u ∈ y) (abs $ prob (a x1 =: u) - prob (a x2 =: u))
            ,  (1 / 2) * sumcmp (u ∈ y) (abs $ sumcmp (v ∈ x) (prob (a v =: u ∧ x1 =: v)) - sumcmp (v ∈ x) (prob (a v =: u ∧ x2 =: v)))
            ,  (1 / 2) * sumcmp (u ∈ y) (abs $ sumcmp (v ∈ x) (prob (a v =: u) * prob (x1 =: v)) - sumcmp (v ∈ x) (prob (a v =: u) * prob (x2 =: v)))
            ,  (1 / 2) * sumcmp (u ∈ y) (abs $ sumcmp (v ∈ x) $ pars $ prob (a v =: u) * prob (x1 =: v) - prob (a v =: u) * prob (x2 =: v))
            ,  (1 / 2) * sumcmp (u ∈ y) (abs $ sumcmp (v ∈ x) $ prob (a v =: u) * (pars $ prob (x1 =: v) - prob (x2 =: v)))
            ]
        s ["Note that we used that", m a_, is, independent, from, m x1, and, m x2, "in equation three"]
        s ["Now we will use the", triangleInequality]
        ma $ (1 / 2) * sumcmp (u ∈ y) (abs $ sumcmp (v ∈ x) $ prob (a v =: u) * (pars $ prob (x1 =: v) - prob (x2 =: v)))
            <= (1 / 2) * sumcmp (u ∈ y) (sumcmp (v ∈ x) $ prob (a v =: u) * (abs $ prob (x1 =: v) - prob (x2 =: v)))
        s ["Finally we use that", m a_, "takes exactly one value of", m y, "for every value of", m x]
        aligneqs ((1 / 2) * sumcmp (u ∈ y) (sumcmp (v ∈ x) $ prob (a v =: u) * (abs $ prob (x1 =: v) - prob (x2 =: v))))
            [ (1 / 2) * sumcmp (v ∈ x) (sumcmp (u ∈ y) $ prob (a v =: u) * (abs $ prob (x1 =: v) - prob (x2 =: v)))
            , (1 / 2) * sumcmp (v ∈ x) ((abs $ prob (x1 =: v) - prob (x2 =: v)) * (sumcmp (u ∈ y) $ prob (a v =: u)))
            , (1 / 2) * sumcmp (v ∈ x) ((abs $ prob (x1 =: v) - prob (x2 =: v)) * 1)
            , statd x1 x2
            ]

statisticalDistanceSubsets :: Note
statisticalDistanceSubsets = thm $ do
    let ii = "I"
        jj = "J"
    s ["Let", m ii, "be a", set, and, m jj, "a", subset, "of", m ii]
    let x = "X"
        y = "Y"
    s ["Let", m x, and, m y, be, randomVariables, over, m ii, and, m jj, respectively]
    ma $ statd x y =: 1 - (setsize jj / setsize ii)

    proof $ do
        let i = "i"
            j = "j"
        aligneqs (statd x y)
            [ (1 / 2) * sumcmp (i ∈ ii) (abs $ prob (x =: i) - prob (y =: i))
            , (1 / 2) * (pars $ sumcmp (i ∈ (ii \\ jj)) (abs $ prob (x =: i) - prob (y =: i)) + sumcmp (j ∈ jj) (abs $ prob (x =: j) - prob (y =: j)))
            , (1 / 2) * (pars $ sumcmp (i ∈ (ii \\ jj)) (abs $ (1 / setsize ii) - 0) + sumcmp (j ∈ jj) (abs $ (1 / setsize ii) - (1 / setsize jj)))
            , (1 / 2) * (pars $ sumcmp (i ∈ (ii \\ jj)) (1 / setsize ii) + sumcmp (j ∈ jj) (abs $ (1 / setsize jj) - (1 / setsize ii)))
            , (1 / 2) * (pars $ sumcmp (i ∈ (ii \\ jj)) (1 / setsize ii) + sumcmp (j ∈ jj) (pars $ (1 / setsize jj) - (1 / setsize ii)))
            , (1 / 2) * (pars $ sumcmp (i ∈ (ii \\ jj)) (1 / setsize ii) + sumcmp (j ∈ jj) (pars $ (1 / setsize jj) - (1 / setsize ii)))
            , (1 / 2) * (pars $ sumcmp (i ∈ (ii \\ jj)) (1 / setsize ii) + sumcmp (j ∈ jj) (1 / setsize jj) - sumcmp (j ∈ jj) (1 / setsize ii))
            , (1 / 2) * (pars $ ((setsize ii - setsize jj) / setsize ii) + (setsize jj / setsize jj) - (setsize jj / setsize ii))
            , (1 / 2) * (pars $ (setsize ii / setsize ii) - (2 * (setsize jj) / setsize ii) + (setsize jj / setsize jj))
            , (1 / 2) * (pars $ 2 - (2 * (setsize jj) / setsize ii))
            , 1 - (setsize jj) / (setsize ii)
            ]



continuousRandomVariables :: Note
continuousRandomVariables = subsubsection "Continuous random variables" $ do
    continuousRandomVariableDefinition
    probabilityDensitySSS
    intervalOpenCloseDistribution


continuousRandomVariableDefinition :: Note
continuousRandomVariableDefinition = de $ do
    s ["A ", randomVariable, " ", m rv_, " in a ", probabilitySpace, " ", m prsp_, " is called ", continuous', " if the image of every point under ", m rv_, " is zero.."]
    ma $ fa (x ∈ univ_) (prob (setof x) =: 0)
    s ["... and the distribution function ", m df_, " is a continuous function"]
    refneeded "continuous function"

  where x = "x"

prdsDec :: Note
prdsDec = s ["Let ", m df_, " be a ", distributionFunction, " of a ", continuous, " ", randomVariable, " ", m rv_, " in a ", probabilitySpace, " ", m prsp_, " that is ", continuous, " with a ", continuous, derivative]

probabilityDensitySSS :: Note
probabilityDensitySSS = note "density" $ do
    probabilityDensitiyFunctionDefinition
    probabilityDensityDistribution
    probabilityDensityDistributionBetween


probabilityDensitiyFunctionDefinition :: Note
probabilityDensitiyFunctionDefinition = de $ do
    lab probabilityDensityFunctionDefinitionLabel
    lab probabilityDensityDefinitionLabel
    lab densityDefinitionLabel
    prdsDec
    s ["The ", probabilityDensityFunction', or, probabilityDensity', " ", m dsf_, " is the following ", function]
    ma $ func dsf_ reals reals x $ prds x =: deriv (prd x) x
  where x = "x"

probabilityDensityDistribution :: Note
probabilityDensityDistribution = thm $ do
    prdsDec
    s ["Let ", m dsf_, " be the ", probabilityDensityFunction, " of ", m rv_]
    ma $ prd a =: prob (x <= a) =: integ minfty a (prds x) x

    toprove
  where
    a = "a"
    x = "x"


probabilityDensityDistributionBetween :: Note
probabilityDensityDistributionBetween = thm $ do
    prdsDec
    s ["Let ", m dsf_, " be the ", probabilityDensityFunction, " of ", m rv_]
    ma $ prd x - prd a =: prob (a < rv_ <= b) =: integ a b (prds x) x

    toprove
  where
    a = "a"
    b = "b"
    x = "x"

intervalOpenCloseDistribution :: Note
intervalOpenCloseDistribution = thm $ do
    s ["Let ", m rv_, " be a ", continuous, " ", randomVariable, " in a ", probabilitySpace, " ", m prsp_, " and let ", m df_, " be the ", distributionFunction, " of ", m rv_]
    ma $ prd (ooint a b)
      =: prd (ocint a b)
      =: prd (coint a b)
      =: prd (ccint a b)

    toprove
  where
    a = "a"
    b = "b"


momentsOfRandomVariables :: Note
momentsOfRandomVariables = subsection "Moments of random variables" $ do
    subsubsection "Expected value and variance" $ do
        note "Expected Value" $ do
            expectedValueDefinition
            expectationOfConstant
            linearityOfExpectation
        note "Covariance" $ do
            covarianceDefinition
        note "Variance" $ do
            varianceDefinition
            varianceInTermsOfExpectation
        note "Standard deviation" $ do
            standardDeviationDefinition
        note "Correlation" $ do
            correlationDefinition

    subsubsection "Sum and product of random variables" $ do
        independenceOfRandomVariables
        sumOfRandomVariablesDefinition
        sumOfRandomVariablesIsRandomVariableTheorem
        expectedValueOfSumTheorem
        varianceOfSumTheorem
        productOfRandomVariablesDefinition
        productOfRandomVariablesIsRandomVariableTheorem
        expectedValueOfProductTheorem

    subsubsection "Higher moments" $ todo "TODO"

expectedValueDefinition :: Note
expectedValueDefinition = de $ do
    lab expectedValueDefinitionLabel
    s ["Let ", m df_, " be a ", distributionFunction, " of a ", continuous, " ", randomVariable, m rv_, " in a ", probabilitySpace, m prsp_, " that is ", continuous, " with a ", continuous, derivative]
    s [the, expectedValue', " of ", m rv_, " is defined as follows"]
    ma $ ev rv_ === integ_ univ_ rv_ prm_ -- TODO two cases
    s ["For a ", discrete, randomVariable, m rv_, " this comes down to the following"]
    ma $ do
        let (i, p, x) = ("i", "p", "x")
        ev rv_ =: sumcmp i (x !: i * p !: i)
    s ["For a ", continuous, randomVariable, m rv_, " this comes down to the following"]
    ma $ do
        let x = "x"
        ev rv_ =: integ minfty pinfty (x * prds x) x

expectationOfConstant :: Note
expectationOfConstant = thm $ do
    lab expectationOfConstantTheoremLabel
    let b = "b"
    s ["Let" , m rv_, "be a", randomVariable, and, m b, "a", constant]
    ma $ ev b =: b
    toprove

linearityOfExpectation :: Note
linearityOfExpectation = thm $ do
    lab linearityOfExpectationTheoremLabel
    let (a, b) = ("a", "b")
    s ["Let", m rv_, "be a", randomVariable, and, m a, and, m b, constants]
    ma $ ev (a * rv_ + b) =: a * ev rv_ + b
    toprove

covarianceDefinition :: Note
covarianceDefinition = de $ do
    lab covarianceDefinitionLabel
    let x = "X"
        y = "Y"
    s ["Let", m x, and, m y, "be two", randomVariables, "in a", probabilitySpace, m prsp_]
    s ["The", covariance', "of", m x, and, m y, "is defined as follows"]
    ma $ cov x y === ev (pars (x - ev x) * pars (y - ev y))

varianceDefinition :: Note
varianceDefinition = de $ do
    lab varianceDefinitionLabel
    s ["Let ", m rv_, " be a ", randomVariable]
    s [the, variance', " of ", m rv_, " is defined as follows"]
    ma $ var rv_ === cov rv_ rv_ =: (ev $ (pars $ rv_ - ev rv_) ^ 2)

varianceInTermsOfExpectation :: Note
varianceInTermsOfExpectation = thm $ do
    lab varianceInTermsOfExpectationTheoremLabel
    s ["Let ", m rv_, " be a ", randomVariable]
    ma $ var rv_ =: ev (rv_ ^ 2) - (ev rv_) ^ 2
    proof $ do
        aligneqs
            (var rv_)
            [
              ev $ (pars $ rv_ - ev rv_) ^ 2
            , ev $ rv_ ^ 2 + (ev rv_) ^ 2 - 2 * rv_ * ev rv_
            , ev (rv_ ^ 2) + ev ((ev rv_) ^ 2) + ev (- 2 * rv_ * ev rv_)
            , ev (rv_ ^ 2) + (ev rv_) ^ 2 - 2 * ev rv_ * ev rv_
            , ev (rv_ ^ 2) - (ev rv_) ^ 2
            ]
    refs [
        linearityOfExpectationTheoremLabel
      , expectationOfConstantTheoremLabel
      ]
    toprove

standardDeviationDefinition :: Note
standardDeviationDefinition = de $ do
    lab standardDeviationDefinitionLabel
    s ["Let ", m rv_, " be a ", randomVariable]
    s [the, standardDeviation', " of ", m rv_, " is defined as the square root of the ", variance, " of ", m rv_]
    ma $ sqrt $ var rv_

correlationDefinition :: Note
correlationDefinition = de $ do
    lab correlationDefinitionLabel
    let x = "X"
        y = "Y"
    s ["Let", m x, and, m y, "be two", randomVariables, "in a", probabilitySpace, m prsp_]
    s [the, correlation', "of", m x, and, m y, "is defined as follows"]
    ma $ cor x y === (cov x y /: sqrt (var x * var y))

independenceOfRandomVariables :: Note
independenceOfRandomVariables = de $ do
    lab statisticallyIndependentDefinitionLabel
    s ["Let ", m x, and, m y, " be random variables in ", m prbsp]
    s [m x, and, m y, " are called", statisticallyIndependent', " if and only if every two events ", m (x <= a), and, m (y <= b), " are ", independent_, " events"]
  where
    a = "a"
    b = "b"
    x = "X"
    y = "Y"


sumOfRandomVariablesDefinition :: Note
sumOfRandomVariablesDefinition = de $ do
    let x = "X"
        y = "Y"
    s ["Let ", m x, and, m y, "be", randomVariables]
    s [the, "sum", m $ x + y, "of", m x, and, m y, " is defined as follows"]
    ma $ fn (pars $ x + y) omega =: fn x omega + fn y omega

sumOfRandomVariablesIsRandomVariableTheorem :: Note
sumOfRandomVariablesIsRandomVariableTheorem = thm $ do
    s [the, sum, "of two", randomVariables, "is a", randomVariable]
    toprove

expectedValueOfSumTheorem :: Note
expectedValueOfSumTheorem = thm $ do
    let x = "X"
        y = "Y"
    s ["Let ", m x, and, m y, "be", randomVariables, "in a", probabilitySpace, m prsp_]
    ma $ ev (x + y) =: ev x + ev y
    toprove

varianceOfSumTheorem :: Note
varianceOfSumTheorem = thm $ do
    let x = "X"
        y = "Y"
    s ["Let ", m x, and, m y, "be", randomVariables, "in a", probabilitySpace, m prsp_]
    ma $ var (x + y) =: var x + var y
    toprove


productOfRandomVariablesDefinition :: Note
productOfRandomVariablesDefinition = de $ do
    let x = "X"
        y = "Y"
    s ["Let ", m x, and, m y, "be", randomVariables]
    s [the, "product", m $ x * y, "of", m x, and, m y, " is defined as follows"]
    ma $ fn (pars $ x * y) omega =: fn x omega * fn y omega


productOfRandomVariablesIsRandomVariableTheorem :: Note
productOfRandomVariablesIsRandomVariableTheorem = thm $ do
    s [the, product, "of two", randomVariables, "is a", randomVariable]
    toprove


expectedValueOfProductTheorem :: Note
expectedValueOfProductTheorem = thm $ do
    let x = "X"
        y = "Y"
    s ["Let ", m x, and, m y, "be", independent, randomVariables, "in a", probabilitySpace, m prsp_]
    ma $ ev (x * y) =: ev x * ev y


inequalitiesSS :: Note
inequalitiesSS = subsection "Inequalities" $ do
    empiricalMeanDefinition
    hoeffdingsInequalityTheorem
    lemmaOnMultiArgumentProbabilities

-- TODO move this?
empiricalMeanDefinition :: Note
empiricalMeanDefinition = de $ do
    lab empiricalMeanDefinitionLabel
    lab sampleMeanDefinitionLabel
    let x = "X"
        n = "n"
        i = "i"
        (_, _, _, xi, xs) = buildiList x n i
        xx = mathcal x
    s ["Let", m xs, "be", xRvs xx]
    s [the, empiricalMean', or, sampleMean', m $ emean x, "of", m xs, "is defined as follows"]
    ma $ emean x =: sumcmpr (i =: 1) n xi

hoeffdingsInequalityTheorem :: Note
hoeffdingsInequalityTheorem = do
    let x = "X"
        n = "n"
        i = "i"
        (_, _, _, xi, xs) = buildiList x n i
        a = "a"
        (_, _, _, ai, as) = buildiList a n i
        b = "b"
        (_, _, _, bi, bs) = buildiList b n i
    let t = "t"
    thm $ do
        lab hoeffdingsInequalityTheoremLabel
        s ["Let", m xs, be, independent, randomVariables <> ", each", m xi, "bounded by an interval", m $ ccint ai bi, "for real numbers", m as, and, m bs]
        ma $ prob ((pars $ emean x - ev (emean x)) >= t) <= exp (- (2 * n ^ 2 * t ^ 2) / (sumcmpr (i =: 1) n ((pars $ bi - ai) ^ 2)))
        ma $ prob ((abs  $ emean x - ev (emean x)) >= t) <= 2 * exp (- (2 * n ^ 2 * t ^ 2) / (sumcmpr (i =: 1) n ((pars $ bi - ai) ^ 2)))
        s ["These inequalities can also be expressed in terms of the sum of", m xs, "as follows"]
        let sn = "S" !: n
        ma $ sn =: sumcmpr (i =: 1) n xi
        ma $ prob ((pars $ sn - ev sn) >= t) <= exp (- (2 * t ^ 2) / (sumcmpr (i =: 1) n ((pars $ bi - ai) ^ 2)))
        ma $ prob ((abs  $ sn - ev sn) >= t) <= 2 * exp (- (2 * t ^ 2) / (sumcmpr (i =: 1) n ((pars $ bi - ai) ^ 2)))

        s ["Where these inequalities are valid for positive values of", m t]
        toprove_ "Maybe don't prove it myself, just reference a paper?"

    con $ do
        s ["If all", m ai, are, m 0, "and all", m bi, "are", m 1, "then we have the following more specific inequality"]
        ma $ prob ((pars $ emean x - ev (emean x)) >= t) <= exp (- 2 * n * t ^ 2)
        toprove_ "Maybe don't prove it myself, just reference the paper? But definitely have a separate proof"

    con $ do
        let a = alpha
        s ["Let", m $ a ∈ ooint 0 1, "and let", m xs, be, independent, and, "identically distributed", xRvs $ setofs [0, 1], "as follows"]
        let p = "p"
        ma $ fa i $ prob (xi =: 1) =: p
        s [hoeffdingsInequality, "then finds us the following bounds"]
        ma $ prob (sumcmpr (i =: 1) n xi <= (pars $ p - a) * n) <= exp (- 2 * a ^ 2 * n)
        ma $ prob (sumcmpr (i =: 1) n xi >= (pars $ p + a) * n) <= exp (- 2 * a ^ 2 * n)



lemmaOnMultiArgumentProbabilities :: Note
lemmaOnMultiArgumentProbabilities = lem $ do
    let sss = mathcal "S"
        ttt = mathcal "T"
        xxx = mathcal "X"
    s ["Let", m sss, and, m ttt, be, finite, sets, and, define, m $ xxx =: sss ⨯ ttt]
    let ss = "S"
        tt = "T"
    s ["Let", m $ prdis_ ss, and, m $ prdis_ tt, "be two", probabilityDistributions, "of", an, xRv ss, and, xRv tt, respectively]
    newline
    let m_ = mu
        mm = fn2 m_
        e = epsilon
        es = e !: ss
        et = e !: tt
    s ["For every", m $ es ∈ (ccint 0 1), and, m $ et ∈ (ccint 0 1), "and every", function, m $ fun m_ (sss ⨯ ttt) (ccint 0 1), "the following holds"]
    ma $ evms [ss, tt] (mm ss tt) <= prdis ss (evm tt (mm ss tt) >= es) + prdis tt (evm ss (mm ss tt) >= et) + es + et

    proof $ do
        let s' = sss <> "'"
            t' = ttt <> "'"
            s_ = "s"
            t_ = "t"
        s ["Let", m s', and, m t', "be two", sets, "defined as follows"]
        ma $ s' =: setcmpr (s_ ∈ sss) (evm tt (mm ss tt) >= es)
        ma $ t' =: setcmpr (t_ ∈ ttt) (evm ss (mm ss tt) >= et)
        let s'' = sss <> "''"
            t'' = ttt <> "''"
        s ["Also define", m $ s'' =: sss \\ s', and, m $ t'' =: ttt \\ t']
        s ["Now note the following", set, "equality"]
        ma $ sss ⨯ ttt =§= (pars $ s' ⨯ t') ∪ (pars $ s'' ⨯ ttt) ⨯ (pars $ sss ⨯ t'')
        s ["We will bound the expression", m $ evms [ss, tt] (mm ss tt), "using the above equality, but first recall what it means"]
        ma $ evms [ss, tt] (mm ss tt) =: sumcmp (tuple s_ t_ ∈ (sss ⨯ ttt)) ((prdis ss $ ss =: s_) * (prdis tt $ tt =: t_) * (mm s_ t_))
        s ["First observe the following three equations"]
        enumerate $ do
            item $ do
                ma $ leftBelowEachOther
                    [ sumcmp (tuple s_ t_ ∈ (s' ⨯ t')) ((prdis ss $ ss =: s_) * (prdis tt $ tt =: t_) * (mm s_ t_))
                    , "" <= sumcmp (tuple s_ t_ ∈ (s' ⨯ t')) ((prdis ss $ ss =: s_) * (prdis tt $ tt =: t_))
                    , "" =: sumcmp (s_ ∈ s') (prdis ss $ ss =: s_) * sumcmp (t_ ∈ t') (prdis tt $ tt =: t_)
                    , "" =: prdis ss (ss ∈ s') * prdis tt (tt ∈ t')
                    , "" =: (prdis ss (evm tt (mm ss tt) >= es) * prdis tt (evm ss (mm ss tt) >= et))
                    ]
                s ["This equality holds because", m $ mm s_ t_, "is upper-bounded by", m 1, "for every", m $ s_ ∈ sss, and, m $ t_ ∈ ttt]
            item $ do
                ma $ leftBelowEachOther
                    [ sumcmp (tuple s_ t_ ∈ (s'' ⨯ ttt)) ((prdis ss $ ss =: s_) * (prdis tt $ tt =: t_) * (mm s_ t_))
                    , "" =: sumcmp (s_ ∈ s'') (pars $ (prdis ss $ ss =: s_) * sumcmp (t_ ∈ ttt) ((prdis tt $ tt =: t_) * (mm s_ t_)))
                    , "" =: sumcmp (s_ ∈ s'') (pars $ (prdis ss $ ss =: s_) * evm tt (mm s_ tt))
                    , "" <= prdis ss (ss ∈ s'') * es
                    , "" <= es
                    ]
                s ["Note that the third step is valid because of how", m s'', "is defined"]
                s ["The following equation holds analogously"]
            item $ do
                ma $ leftBelowEachOther
                    [ sumcmp (tuple s_ t_ ∈ (sss ⨯ t'')) ((prdis ss $ ss =: s_) * (prdis tt $ tt =: t_) * (mm s_ t_))
                    , "" =: sumcmp (t_ ∈ t'') (pars $ (prdis tt $ tt =: t_) * sumcmp (s_ ∈ sss) ((prdis ss $ ss =: s_) * (mm s_ t_)))
                    , "" =: sumcmp (t_ ∈ t'') (pars $ (prdis tt $ tt =: t_) * evm ss (mm ss t_))
                    , "" <= prdis tt (tt ∈ t'') * et
                    , "" <= et
                    ]
                s ["Note that the third step is valid because of how", m t'', "is defined"]
        s ["Combining these inequalities completes the proof"]
        ma $ leftBelowEachOther
            [ evms [ss, tt] (mm ss tt)
            , "" =: sumcmp (tuple s_ t_ ∈ (sss ⨯ ttt)) ((prdis ss $ ss =: s_) * (prdis tt $ tt =: t_) * (mm s_ t_))
            , "" =: sumcmp (tuple s_ t_ ∈ (s'  ⨯ t' )) ((prdis ss $ ss =: s_) * (prdis tt $ tt =: t_) * (mm s_ t_))
            , ""  + sumcmp (tuple s_ t_ ∈ (s'' ⨯ ttt)) ((prdis ss $ ss =: s_) * (prdis tt $ tt =: t_) * (mm s_ t_))
            , ""  + sumcmp (tuple s_ t_ ∈ (sss ⨯ t'')) ((prdis ss $ ss =: s_) * (prdis tt $ tt =: t_) * (mm s_ t_))
            , "" <= (prdis ss (evm tt (mm ss tt) >= es) * prdis tt (evm ss (mm ss tt) >= et))
                  + es + et
            ]





