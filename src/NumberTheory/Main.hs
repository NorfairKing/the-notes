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
import           Relations.Basics.Terms
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
    dividesTransitive
    dividesMultiples
    productDivides
    gcdDefinition
    lcmDefinition
    todo "gcdExistence"
    todo "lcmExistence"
    bezoutIdentityLemma
    lcmGcdProduct
    coprimeDivisionCancels
    coprimeDividesProduct
    primeDefinition
    coprimeDefinition
    coprimeCompound
    gcdMultiplicative
    gcdMultiplicativeConsequence

divisibilityDefinition :: Note
divisibilityDefinition = de $ do
    todo "define divisibility more abstractly in integrity domains"
    let a = "a"
    let b = "b"
    let c = "c"
    s ["We define a", wholeNumber, m a, "to be", divisible', "by another", wholeNumber, m b, "if there exists a", wholeNumber, m c, "such that", m $ a `divZ` b =: c]
    s ["We then call", m b, "a", divisor', "of", m a, and, m c, "the", quotient']
    ma $ a .| b === te (c ∈ ints) (a * c =: b)

dividesTransitive :: Note
dividesTransitive = prop $ do
    lab dividesTransitivePropertyLabel
    s [the, divides, relation, is, transitive_]
    let a = "a"
    let b = "b"
    let c = "c"
    ma $ fa (cs [a, b, c] ∈ ints) $ (pars $ a .| b) ∧ (pars $ b .| c) ⇒ (pars $ a .| c)

    proof $ do
        let x = "x"
        s ["Because", m a, divides, m b <> ", there exists an", integer, m x, "as follows"]
        ma $ a * x =: b
        let y = "y"
        s ["Because", m b, divides, m c <> ", there exists an", integer, m y, "as follows"]
        ma $ b * y =: c
        s ["Now we conclude that", m a, divides, m c, with, quotient, m $ x * y]
        ma $ a * x * y =: c



dividesMultiples :: Note
dividesMultiples = prop $ do
    lab dividesMultiplesPropertyLabel
    let a = "a"
    let b = "b"
    let r = "r"
    s ["Let", m a, and, m b, be, integers, "such that", m a, divides, m b]
    ma $ fa (r ∈ ints) $ (a .| b) ⇒ (a .| (r * b))

    proof $ do
        let q = "q"
        s ["Because", m a, divides, m b, "there exists an", integer, m q, "as follows"]
        ma $ a * q =: b
        s ["Let", m r, "be arbitrary"]
        s ["Now, ", m a, divides, m $ r * b, "because of the following equation which we obtain by multiplying", m r, "to both sides of the previous equation"]
        ma $ a * (q * r) =: b * r

productDivides :: Note
productDivides = prop $ do
    lab productDividesPropertyLabel
    let a = "a"
        b = "b"
        c = "c"
        d = "d"
        ab = a * b
        cd = c * d
    s ["Let", csa [m a, m b, m c, m d], be, integers, "such that", m a, divides, m b, and, m c, divides, m d <> ", then", m ab, divides, m cd]
    ma $ (pars $ a .| b) ∧ (pars $ c .| d) ⇒ (ab .| cd)

    proof $ do
        let q = "q"
        s ["Because", m a, divides, m b, "there exists a", m q, "as follows"]
        ma $ a * q =: b
        let r = "r"
        s ["Because", m c, divides, m d, "there exists a", m r, "as follows"]
        ma $ c * q =: d
        s ["When we multiply these equations, we find that", m ab, divides, m cd, with, quotient, m $ q * r]
        ma $ ab * q * r =: cd


gcdDefinition :: Note
gcdDefinition = de $ do
    let a = "a"
        b = "b"
        g = "g"
        c = "c"
    s [the, greatestCommonDivisor', m $ gcd a b, "of two", integers, m a, and, m b, "is defined as follow"]
    ma $ g =: gcd a b  === (pars $ g .| a) ∧ (pars $ g .| b) ∧ (not $ pars $ te (c ∈ ints) $ (pars $ c .| a) ∧ (pars $ c .| b) ∧ (pars $ c .| g))

lcmDefinition :: Note
lcmDefinition = de $ do
    let a = "a"
        b = "b"
        l = "l"
        c = "c"
    s [the, leastCommonMultiple', m $ lcm a b, "of two", integers, m a, and, m b, "is defined as follow"]
    ma $ l =: lcm a b  === (pars $ a .| l) ∧ (pars $ b .| l) ∧ (not $ pars $ te (c ∈ ints) $ (pars $ a .| c) ∧ (pars $ b .| c) ∧ (pars $ c .| l))


bezoutIdentityLemma :: Note
bezoutIdentityLemma = lem $ do
    let a = "a"
        b = "b"
        x = "x"
        y = "y"
    s ["Let", m a, and, m b, "be nonzero", integers, "then there exist", integers, m x, and, m y, "as follows"]
    ma $ a * x + b * y =: gcd a b

    todo "write this down correctly"
    toprove

lcmGcdProduct :: Note
lcmGcdProduct = prop $ do
    let a = "a"
        b = "b"
        ab = a * b
        gab = gcd a b
        lab = lcm a b
    s ["Let", m a, and, m b, be, integers]
    ma $ gab * lab =: a * b

    proof $ do
        let p = "p"
        s ["Because", m gab, divides, m a <> ", it also divides", m ab, ref dividesMultiplesPropertyLabel, "so there exists an", integer, m p, "as follows"]
        ma $ gab * p =: ab
        s ["We now prove that", m p, "equals", m lab]
        itemize $ do
            let x = "x"
            item $ do
                s [m a, divides, m p]
                newline
                s ["Because", m gab, divides, m b <> ", there exists an", m x, "as follows"]
                ma $ gab * x =: b
                s ["Multiply both sides by", m a, "and we get the following"]
                ma $ gab * x * a =: ab
                s ["Equate this with the equation that we found for", m ab, "earlier, and we conclude that", m a, divides, m p, with, quotient, m x]
            let y = "y"
            item $ do
                s [m b, divides, m p]
                newline
                s ["Because", m gab, divides, m a <> ", there exists an", m y, "as follows"]
                ma $ gab * y =: a
                s ["Multiply both sides by", m b, "and we get the following"]
                ma $ gab * y * b =: ab
                s ["Equate this with the equation that we found for", m ab, "earlier, and we conclude that", m b, divides, m p, with, quotient, m y]

            item $ do
                s ["There is no smaller", integer, "like that"]
                newline
                let z = "z"
                s ["Suppose", m z, "is an", integer, "that is", divisible, by, m a, and, m b]
                let k = "k"
                    k1 = k !: 1
                    k2 = k !: 2
                ma $ z =: a * k1 <> quad <> text and <> quad <> z =: b * k2
                let u = "u"
                    v = "v"
                s ["By", bezoutsLemma <> ", there must exist two", integers, m u, and, m v, "as follows"]
                ma $ gab =: a * u + b * v
                s ["Now observe the following"]
                aligneqs (z * gab)
                    [ z * (pars $ a * u + b * v)
                    , z * a * u + z * b * v
                    , (pars $ b * k2) * a * u + (pars $ a * k1) * b * v
                    , (a * b) * (pars $ k2 * u + k1 * v)
                    , (gab * p) * (pars $ k2 * u + k1 * v)
                    ]
                s ["We concude that", m p, divides, m z]
                ma $ z =: p * (pars $ k2 * u + k1 * v)


coprimeDivisionCancels :: Note
coprimeDivisionCancels = prop $ do
    lab coprimeDivisionCancelsPropertyLabel
    let a = "a"
        b = "b"
        c = "c"
        bc = b * c
    s ["Let", csa [m a, m b, m c], be, integers, "such that", m a, divides, m bc, and, m a, and, m c, are, coprime <> ", then", m a, divides, m b]
    ma $ (pars $ a .| bc) ∧ (pars $ a `copr` c) ⇒ (pars $ a .| b)

    proof $ do
        let n = "n"
        s ["Because", m a, divides, m bc <> ", there exists an", integer, m n, "as follows"]
        ma $ n * a =: bc
        let x = "x"
            y = "y"
        s ["By", bezoutsLemma <> ", there must exist two", integers, m x, and, m y, "as follows"]
        ma $ 1 =: a * x + c * y
        s ["Multiply", m b, "on both sides of this equation to obtain the following"]
        ma $ b =: a * b * x + b * c * y
        s ["Now substitute", m bc]
        ma $ b =: a * b * x + a * n * y
        s ["Seperate out", m a, "to conclude that", m a, divides, m b, with, quotient, m $ b * x + n * y]
        ma $ b =: a * (pars $ b * x + n * y)



coprimeDividesProduct :: Note
coprimeDividesProduct = prop $ do
    lab coprimeDividesProductPropertyLabel
    let a = "a"
        b = "b"
        c = "c"
        ab = a * b
    s ["Let", csa [m a, m b, m c], be, integers, "such that", m a, divides, m b, and, m a, divides, m c, and, m a, and, m b, are, coprime <> ", then", m ab, divides, m c]
    ma $ (pars $ a .| c) ∧ (pars $ b .| c) ∧ (pars $ gcd a b =: 1) ⇒ (pars $ ab .| c)

    proof $ do
        let q = "q"
        s ["Because", m a, divides, m c, "there exists a", m q, "as follows"]
        ma $ a * q =: c
        s ["Because", m b, divides, m $ a * q, but, m a, and, m b, are, coprime, "we conclude that", m b, divides, m q, ref coprimeDivisionCancelsPropertyLabel]
        s ["Because", m b, divides, m q, "there must exist an", integer, m p, "as follows"]
        let p = "p"
        ma $ b * p =: q
        s ["We now find that", m ab, divides, m c, with, quotient, m p]
        ma $ a * b * p =: c



primeDefinition :: Note
primeDefinition = de $ do
    let a = "a"
    s ["An", integer, m a, "is called", prime', "if it its largest", divisor <> ", different from", m a, "itself, is", m 1]

coprimeDefinition :: Note
coprimeDefinition = de $ do
    let a = "a"
        b = "b"
    s ["Two", integers, m a, and, m b, "are considered", cso [coprime', relativelyPrime', mutuallyPrime], "if their", greatestCommonDivisor, "is one"]
    ma $ a `copr` b === gcd a b =: 1
    s ["Equivalently, their", leastCommonMultiple, is, m $ a * b]
    toprove

coprimeCompound :: Note
coprimeCompound = prop $ do
    lab coprimeCompoundPropertyLabel
    let a = "a"
        b = "b"
        c = "c"
    s ["Let", csa [m a, m b, m c], be, integers, "such that", m a, and, m b, are, coprime <> ", then", m $ gcd a c, and, m $ gcd b c, are, coprime]
    ma $ (a `copr` b) ⇒ fa (c ∈ ints) (gcd a c `copr` gcd b c)

    proof $ do
        s ["Suppose, for the sake of contradiction, that", m $ gcd a c, and, m $ gcd b c, "are not", coprime]
        s ["This would mean the following"]
        let g = "g"
        ma $ gcd (gcd a c) (gcd b c) =: g > 1
        s ["This means that", m g, divides, m $ gcd a c, and, m $ gcd b c, and, "therefore transitively", m a, and, m b, ref dividesTransitivePropertyLabel]
        s ["Because", m a, and, m b, are, coprime, "the", greatestCommonDivisor, "of", m a, and, m b, is, m 1, "so", m g, "cannot be a", divisor, "of", m a, and, m b]
        s ["We arrive at a contradiction"]

gcdMultiplicative :: Note
gcdMultiplicative = prop $ do
    let a = "a"
        b = "b"
        c = "c"
    s ["Let", csa [m a, m b, m c], be, integers, "such that", m a, and, m b, are, coprime]
    let ab = a * b
        gab = gcd ab c
        ga = gcd a c
        gb = gcd b c
        gab_ = ga * gb
    ma $ gab =: ga * gb

    proof $ do
        s ["We prove the three components of the", greatestCommonDivisor, "separately"]
        itemize $ do
            item $ do
                s [m gab_, divides, m ab, ref productDividesPropertyLabel]
            item $ do
                s [m gab_, divides, m c, ref coprimeDividesProductPropertyLabel]
            item $ do
                s [m gab_, "is the smallest", integer, "that does so"]
            todo "not done here"


gcdMultiplicativeConsequence :: Note
gcdMultiplicativeConsequence = con $ do
    let a = "a"
        b = "b"
        c = "c"
    s ["Let", csa [m a, m b, m c], be, integers, "such that", m a, and, m b, are, coprime]
    s [m a, and, m $ b * c, are, coprime, "if and only if both", m a, and, m b <> ",", and, m a, and, m c, are, coprime]

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

