module NumberTheory.Main where

import           Notes

import qualified Data.Text                       as T
import qualified Prelude                         as P (Int, map, mod, (+), (<),
                                                       (^))

import           Functions.Basics.Macro
import           Functions.BinaryOperation.Terms
import           Functions.Jections.Terms
import           Groups.Macro
import           Groups.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Relations.Equivalence.Macro
import           Relations.Equivalence.Terms
import           Sets.Basics.Terms

import           NumberTheory.Macro
import           NumberTheory.Terms

numberTheoryC :: Note
numberTheoryC = chapter "Number Theory" $ do
    naturalNumbersS
    wholeNumbersS
    divisibilityS
    moduloS

naturalNumbersS :: Note
naturalNumbersS = section "Natural numbers" $ do
    naturalNumbersDefinition
    naturalNumbersAddition
    naturalNumbersSubtraction
    naturalNumbersMultiplication
    naturalNumbersDivision

naturalNumbersDefinition :: Note
naturalNumbersDefinition = de $ do
    s [naturalNumbers', m nats, "are inductively defined as follows"]
    itemize $ do
        item $ m $ 0 === emptyset
        let n = "n"
        item $ m $ succ n === n ∪ setof n

naturalNumbersAddition :: Note
naturalNumbersAddition = de $ do
    s [the, addition', "of", naturalNumbers, "is a", binaryOperation, m addN_, "defined recursively as follows"]
    let n = "n"
    ma $ n `addN` 0 === n === 0 `addN` n
    let m = "m"
    ma $ succ n + m === succ (n `addN` m)

naturalNumbersSubtraction :: Note
naturalNumbersSubtraction = de $ do
    s [the, subtraction', "of", naturalNumbers, "is a", binaryOperation, m subN_, "defined in terms of", addition, "as follows"]
    let a = "a"
    let b = "b"
    let c = "c"
    s ["We say that", m $ a `subN` b =: c, "holds if", m $ c `addN` b =: a, "holds"]


naturalNumbersMultiplication :: Note
naturalNumbersMultiplication = de $ do
    s [the, multiplication', "of", naturalNumbers, "is a", binaryOperation, m mulN_, "defined in terms of", addition, "as follows"]
    let n = "n"
    ma $ n `mulN` 0 === 0 === 0 `mulN` n
    ma $ n `mulN` 1 === n === 1 `mulN` n
    let m = "m"
    ma $ succ n `mulN` m === m `addN` (pars $ n `mulN` m)


naturalNumbersDivision :: Note
naturalNumbersDivision = de $ do
    s [the, division', "of", naturalNumbers, "is a", binaryOperation, m divN_, "defined in terms of", multiplication, "as follows"]
    let a = "a"
    let b = "b"
    let c = "c"
    s ["We say that", m $ a `divN` b =: c, "holds if", m $ c `mulN` b =: a, "holds"]
    s [m $ a `divN` b, "is often written as", m $ a / b]


wholeNumbersS :: Note
wholeNumbersS = do
    wholeNumbersDefinition
    wholeNumbersEquivalentDefinition
    naturalNumbersSubsetofWholeNumbersUnderInjection
    wholeNumbersAddition
    wholeNumbersSubtraction
    wholeNumbersMultiplication
    wholeNumbersDivision


wholeNumbersDefinition :: Note
wholeNumbersDefinition = de $ do
    s [wholeNumbers', or, integers', m ints, "are defined as the", equivalenceClasses, "of", m $ naturals ^ 2, "with respect to the following", equivalenceRelation]
    let (a, b, c, d) = ("a", "b", "c", "d")
    -- b - a = d - c
    ma $ wholen a b .~ wholen c d === b + c =: d + a
    nte $ do
        s ["Intuitively, an", element, m $ wholen a b, "represents", m $ b - a, "even if that", element, "does not exist in", m nats]

wholeNumbersEquivalentDefinition :: Note
wholeNumbersEquivalentDefinition = nte $ do
    let pos = "+"
        neg = "-"
    s [wholeNumbers, "can equivalently be defined using two abstract elements", m pos, and, m neg, "as the", set, m $ setofs [pos, neg] ⨯ nats]
    s ["Then there is no need to use", equivalenceClasses, "but we have to come up with suitable definitions of", m pos, and, m neg]
    s ["For example, we can use the following definitions"]
    ma $ pos === emptyset <> qquad <> text and <> qquad <> neg === setof emptyset

naturalNumbersSubsetofWholeNumbersUnderInjection :: Note
naturalNumbersSubsetofWholeNumbersUnderInjection = nte $ do
    let i = "i"
    s ["We regard the", set, "of", naturalNumbers, "as a", subset, "of the", wholeNumbers, "under the following", injection, m i]
    let a = "a"
    ma $ func i nats ints a $ wholen 0 a

wholeNumbersAddition :: Note
wholeNumbersAddition = de $ do
    s [the, addition, m addZ_, "of", wholeNumbers, "is defined as the component-wise", addition, "of", naturalNumbers]
    let (a, b, c, d) = ("a", "b", "c", "d")
    ma $ wholen a b `addZ` wholen c d === wholen (a `addN` c) (b `addN` d)
    s ["As such, we abbreviate", m $ wholen 0 a, "as", m a]

wholeNumbersSubtraction :: Note
wholeNumbersSubtraction = de $ do
    s [the, subtraction', "of", wholeNumbers, "is a", binaryOperation, m subZ_, "defined in terms of", addition, "as follows"]
    let a = "a"
    let b = "b"
    let c = "c"
    s ["We say that", m $ a `subZ` b =: c, "holds if", m $ c `addZ` b =: a, "holds"]

wholeNumbersMultiplication :: Note
wholeNumbersMultiplication = de $ do
    s [the, multiplication', "of", wholeNumbers, "is a", binaryOperation, m mulZ_, "defined in terms of", addition, "as follows"]
    let n = "n"
    ma $ n `mulZ` 0 === 0 === 0 `mulZ` n
    ma $ n `mulZ` 1 === n === 1 `mulZ` n
    let m = "m"
    ma $ succ n `mulZ` m === m `addZ` (pars $ n `mulZ` m)

wholeNumbersDivision :: Note
wholeNumbersDivision = de $ do
    s [the, division', "of", wholeNumbers, "is a", binaryOperation, m divN_, "defined in terms of", multiplication, "as follows"]
    let a = "a"
    let b = "b"
    let c = "c"
    s ["We say that", m $ a `divZ` b =: c, "holds if", m $ c `mulZ` b =: a, "holds"]
    s [m $ a `divZ` b, "is often written as", m $ a / b]

divisibilityS :: Note
divisibilityS = section "Divisibilty" $ do
    divisibilityDefinition
    gcdDefinition
    lcmDefinition
    primeDefinition
    coprimeDefinition

divisibilityDefinition :: Note
divisibilityDefinition = de $ do
    todo "define divisibility more abstractly in integrity domains"
    let a = "a"
    let b = "b"
    let c = "c"
    s ["We define a", wholeNumber, m a, "to be", divisible', "by another", wholeNumber, m b, "if there exists a", wholeNumber, m c, "such that", m $ a `divZ` b =: c]
    s ["We then call", m b, "a", divisor', "of", m a]
    ma $ a .| b === te (c ∈ ints) (a * c =: b)

gcdDefinition :: Note
gcdDefinition = de $ do
    let a = "a"
        b = "b"
        g = "g"
        c = "c"
    s [the, greatestCommonDenominator', m $ gcd a b, "of two", integers, m a, and, m b, "is defined as follow"]
    ma $ g =: gcd a b  === (pars $ g .| a) ∧ (pars $ g .| b) ∧ (not $ pars $ te (c ∈ ints) $ (pars $ c .| a) ∧ (pars $ c .| b) ∧ (pars $ c > g))

lcmDefinition :: Note
lcmDefinition = de $ do
    let a = "a"
        b = "b"
        l = "l"
        c = "c"
    s [the, leastCommonMultiple', m $ lcm a b, "of two", integers, m a, and, m b, "is defined as follow"]
    ma $ l =: lcm a b  === (pars $ a .| l) ∧ (pars $ b .| l) ∧ (not $ pars $ te (c ∈ ints) $ (pars $ a .| c) ∧ (pars $ b .| c) ∧ (pars $ c < l))

primeDefinition :: Note
primeDefinition = de $ do
    let a = "a"
    s ["An", integer, m a, "is called", prime', "if it its largest", divisor <> ", different from", m a, "itself, is", m 1]

coprimeDefinition :: Note
coprimeDefinition = de $ do
    let a = "a"
        b = "b"
    s ["Two", integers, m a, and, m b, "are considered", cso [coprime', relativelyPrime', mutuallyPrime], "if their", greatestCommonDenominator, "is one"]
    ma $ a `copr` b === gcd a b =: 1
    s ["Equivalently, their", leastCommonMultiple, is, m $ a * b]
    toprove

moduloS :: Note
moduloS = section "Modular arithmetic" $ do
    modularIntegersDefinition
    quadraticResidueDefinition
    quadraticResidueExamples
    chineseRemainderTheorem

modularIntegersDefinition :: Note
modularIntegersDefinition = de $ do
    let n = "n"
    s [the, integers, "modulo an", integer, m n, "are defined as the following", quotientGroup]
    ma $ intmod n === qgrp ints (n <> ints)
    todo "fully formalize once we have a good chapter on groups"

quadraticResidueDefinition :: Note
quadraticResidueDefinition = de $ do
    lab quadraticResidueDefinitionLabel
    let n = "n"
        x = "r"
        y = "q"
    s ["A", quadraticResidue', "modulo an", integer, m n, "is an", integer, m x, "such that there exists an", integer, m y, "as follows"]
    ma $ eqmod n (y ^ 2) x

quadraticResidueExamples :: Note
quadraticResidueExamples = do
    ex $ do
        let n = "n"
        s [m 0, and, m 1, "are always", quadraticResidues, "in", m $ intmod n, for, m $ n > 1, because, m $ eqmod n (0 ^ 2) 0, and, m $ eqmod n (1 ^ 2) 1]
    ex $ do
        s ["In", m (intmod 7) <> ",", m 2, "is a", quadraticResidue, because, m $ eqmod 7 (5 ^ 2) 2]
    ex $ do
        s ["In", m $ intmod 5, ", the", quadraticResidues, are, csa [m 0, m 1, m 4], because, csa [m $ eqmod 5 (0 ^ 2) 0, m $ eqmod 5 (1 ^ 2) 1, m $ eqmod 5 (2 ^ 2) 4]]
    ex $ do
        s ["In", m $ intmod 35, ", the", quadraticResidues, are, "the following", elements]
        ma $ cs [0, 1, 4, 9, 11, 14, 15, 16, 21, 25, 29, 30]
    ex $ do
        s ["Here are the", quadraticResidues, "(different from", m 0, and, m 1 <> ") modulo some small", integers]
        let rawn :: P.Int -> Note
            rawn = raw . T.pack . show
        let n = 20
        newline
        hereFigure $ linedTable
            ((raw "q\\setminus n") : P.map rawn [1 .. n])
            ( P.map (\i -> do
                rawn i : (P.map (\j -> if j P.< (i P.+ 1) then (rawn $ j P.^ (2 :: P.Int) `P.mod` i) else mempty) [1 .. n])
                ) [0 .. n])

chineseRemainderTheorem :: Note
chineseRemainderTheorem = thm $ do
    let n = "n"
        k = "k"
        a = "a"
        (n1, n2, nk, ns) = buildList n k
        (a1, a2, ak, as) = buildList a k
    s ["Let", m ns, "be a list of", pairwiseCoprime, integers]
    let x = "x"
    s ["For any given list of", integers, m as <> ", there exists an", integer, m x, "as follows"]
    ma $ centeredBelowEachOther $
        [ eqmod n1 x a1
        , eqmod n2 x a2
        , vdots
        , eqmod nk x ak
        ]
    let i = "i"
    let ni = n !: i
    s ["Furthermore, the solution is unique modulo", m $ prodcmp i ni]

    proof $ do
        let nn = "N"
        s ["Let", m nn, "be the product", m $ prodcmpr (i =: 1) k ni]
        let nni = nn !: i
        s ["Define", m nni, "as", m $ nn / nk]
        newline
        s ["Because the", integers, m ns, are, pairwiseCoprime <> ",", m nni, and, m ni, "are also", coprime]
        ma $ gcd nni ni =: 1
        why
        todo "Finish this proof"

