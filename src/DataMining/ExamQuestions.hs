module DataMining.ExamQuestions where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Distances.Macro
import           Functions.SetFunctions.Terms
import           Sets.Basics.Terms

extraExamQuestions :: Note
extraExamQuestions = do
    dmSubmodularFunctionQuestion
    dmSubmodularFunctionProbabilityQuestion

dmSubmodularFunctionQuestion :: Note
dmSubmodularFunctionQuestion = do
    examq eth "Data Mining" "2013"
    let v = mathcal "V"
        pv = powset v
        n = "n"
        x = "x"
        p = "p"
    -- TODO index datapoint
    s ["Let", m v, "be a set of", m n, "data points", m $ setlist (x !: 1) (x !: 2) (x !: n) ⊆ reals ^ p]
    let l' = "L"
        l = fn l'
        as = mathcal "A"
    s ["Define a", setFunction, m l', "as follows"]
    let i = "i"
        j = "j"
        xi = x !: i
        xj = x !: j
        n = (^2) . norm
    ma $ func l' pv reals as $ l as =: sumcmp (xi ∈ v) (min (xj ∈ as) $ n $ xi - xj)
    let f' = mathcal "F"
        f = fn f'
        ss = mathcal "S"
    let a = "a"
    s ["Also define", m f', "as follows for a given", m a]
    let sa = setof a
        ss' = ss ∪ sa
    ma $ func f' pv reals ss $ f ss =: l sa - l ss'
    thm $ do
        s [m f', "is a", submodular_, function]
        proof $ do
            let h' = "H" !: xi
                h = fn h'
            s ["First we prove that the following function", m h', "is", submodular, "for any", m $ xi ∈ v]
            ma $ func h' pv reals as $ h as =: - min (xj ∈ as) (n $ xi - xj)
            let x = "X"
                y = "Y"
                z = "z"
            let sz = setof z
                x' = x ∪ sz
                y' = y ∪ sz
            s ["Let", m x, and, m y, "be sets in", m $ powset v, "such that", m x, "is a subset of", m y, and, "let", m z, "be an element of", m $ v \\ y]
            ma $ h x' - h x >= h y' - h y
            ma $
                (min (xj ∈ x) (n $ xi - xj) - min (xj ∈ x') (n $ xi - xj))
                >=
                (min (xj ∈ y) (n $ xi - xj) - min (xj ∈ y') (n $ xi - xj))

            s ["We take a look at the right part"]
            ma $ (min (xj ∈ y) (n $ xi - xj) - min (xj ∈ y') (n $ xi - xj))
            s ["This is either zero or strictly positive"]
            newline
            s ["It is exactly zero if", m $ n $ xi - z, "is not smaller than", m $ min (xj ∈ y) (n $ xi - xj)]
            s ["In this case", m $ n $ xi - z, "is definitely not smaller than", m $ min (xj ∈ x) (n $ xi - xj), "because", m $ x ⊆ y, "holds"]

            newline
            s ["It is strictly positive if the following holds"]
            ma $ n (xi - z) < min (xj ∈ y) (n $ xi - xj)
            ma $ n (xi - z) =: min (xj ∈ y') (n $ xi - xj)
            s ["... and by extension the following because", m $ x ⊆ y, "holds"]
            ma $ n (xi - z) =: min (xj ∈ x') (n $ xi - xj)

            let w = "w"
            s ["The value for which the minimum on the rightand side is achieved, we will call", m w]
            ma $ min (xj ∈ y) (n $ xi - xj) =: n (xi - w)
            s ["Now there are two cases"]
            s ["Either ", m w, "is an element of", m x, "or it is an element of", m $ y \\ x]
            newline

            s ["In the first case, the following also holds and by extension the inequality"]
            ma $ min (xj ∈ x) (n $ xi - xj) =: n (xi - w)
            ma $
                (n (xi - w) - n (xi - z))
                >=
                (n (xi - w) - n (xi - z))

            s ["In the second case, the following holds"]
            ma $ min (xj ∈ x) (n $ xi - xj) > n (xi - w)
            s ["... and by extension again the inequality"]
            ma $
                (n (xi - w) - min (xj ∈ x') (n $ xi - xj))
                >=
                (n (xi - w) - min (xj ∈ y') (n $ xi - xj))
            newline
            s ["Because the sum of", submodular, functions, "is", submodular, ref submodularityIsClosedUnderNonnegativeLinearCombinationTheoremLabel, ", this means that", m $ - l', "as follows is submodular"]
            ma $ fn (- l') as =: - sumcmp (xi ∈ v) (min (xj ∈ as) $ n $ xi - xj)

            s ["We will now show that this means that", m f', "is submodular"]
            newline

            let x = "X"
                y = "Y"
                z = "z"
            s ["Let", m x, and, m y, "be sets in", m $ powset v, "such that", m x, "is a subset of", m y, and, "let", m z, "be an element of", m $ v \\ y]
            let x' = x ∪ sa
                y' = y ∪ sa
                x'' = x ∪ setofs [a, z]
                y'' = y ∪ setofs [a, z]
            ma $ centeredBelowEachOther
                [
                  l x' - l x'' >= l y' - l y''
                , l x' - l sa + l sa - l x'' >= l y' - l sa + l sa - l y''
                , (l sa - l x'') - (l sa - l x') >= (l sa - l y'') - (l sa - l y')
                , f x'' - f x' >= f y'' - f y'
                ]
            s ["This concludes the proof that", m f', "is", submodular]

    let k = "k"
    s ["Using the submodularity property of", m f', "we can solve the examplar based", m k, "-means problem when one of the", m k, "centers is fixed to be", m a]
    -- TODO define NP hard and index it here
    s ["Computing an optimal solution to this maximization problem is NP-hard, but because ", m f', "is submodular, we can take a greedy approach to approximate the solution"]

    s ["In every step, we "]
    let a = (!:) (mathcal "A")
    hereFigure $ do
        renderAlgorithm $ do
            a 0 <-. setof "a"
            lnbk
            forS (i =: 1 <> ".." <> pars (k - 1)) $ do
                let ss = "s"
                    ss' = ss ^: "*"
                ss' <-. argmax ss (f $ (a $ i - 1) ∪ setof ss)
                lnbk
                a i <-. (a (i - 1) ∪ setof ss')
        caption $ "A greedy algorithm to approximate " <> m ("S" ^: "*")


dmSubmodularFunctionProbabilityQuestion :: Note
dmSubmodularFunctionProbabilityQuestion = do
    examq eth "Data Mining" "2014"
    let v = mathcal "V"
        pv = powset v
        g' = "G"
        g = fn g'
    s ["Let", m v, "be a", finite, set, "and let", m g', "be a", submodular, function]
    ma $ fun g' pv reals
    -- TODO index probability distribution
    let ss = "S"
    s ["Let", m $ ss ⊆ v, "be drawn at random from some probability distribution over", m $ powset v]
    thm $ do
        let f' = "F"
            f = fn f'
        s ["The", function, m f', ", defined as follows, is", submodular]
        let a = "A"
            prob = fn "P"
        ma $ func f' pv reals a $ f a =: (sumcmp (ss ⊆ v) $ prob ss * g (v \\ (pars $ a ∩ ss)))
        proof $ do
            let e' = "E" !: ss
                e = fn e'
            s ["Because of the closedness under random processes", ref submodularityIsClosedUnderRandomProcessesTheoremLabel, "we only need to prove that the following function", m e', "is", submodular, "for a given", m $ ss ⊆ v]
            ma $ func e' pv reals a $ e a =: g (v \\ (pars $ a ∩ ss))

            let x = "X"
                y = "Y"
                z = "z"
                x' = x ∪ setof z
                y' = y ∪ setof z
            s ["Let", m x, and, m y, "be subsets of", m v, "such that", m $ x ⊆ y, "holds"]
            s ["Let", m z, "be an element of", m $ v \\ y]

            todo "FIX THIS LATER"
            ma $ centeredBelowEachOther
                [
                  g (v \\ (pars $ pars x' ∩ ss)) - g (v \\ (pars $ x ∩ ss)) >= g (v \\ (pars $ pars y' ∩ ss)) - g (v \\ (pars $ y ∩ ss))
                , e x' - e x >= e y' - e y
                ]

