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
    ma $ g =: gcd a b  === (pars $ g .| a) ∧ (pars $ g .| b) ∧ (not $ pars $ te (c ∈ ints) $ (pars $ c .| a) ∧ (pars $ c .| b) ∧ (pars $ c < g))

lcmDefinition :: Note
lcmDefinition = de $ do
    let a = "a"
        b = "b"
        l = "l"
        c = "c"
    s [the, leastCommonMultiple', m $ lcm a b, "of two", integers, m a, and, m b, "is defined as follow"]
    ma $ l =: lcm a b  === (pars $ a .| l) ∧ (pars $ b .| l) ∧ (not $ pars $ te (c ∈ ints) $ (pars $ a .| c) ∧ (pars $ b .| c) ∧ (pars $ c < l))


bezoutIdentityLemma :: Note
bezoutIdentityLemma = lem $ do
    lab bezoutsIdentityLemmaLabel
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
    lab gcdMultiplicativePropertyLabel
    let a = "a"
        b = "b"
        c = "c"
    s ["Let", csa [m a, m b, m c], be, integers, "such that", m a, and, m b, are, coprime]
    let ab = a * b
        gab = gcd ab c
        ga = gcd a c
        gb = gcd b c
        gab_ = ga * gb
        g = "g"
    ma $ gab =: ga * gb

    proof $ do
        s ["We prove the three components of the", greatestCommonDivisor, "separately"]
        s ["Define", m $ g =: gab_]
        itemize $ do
            item $ do
                s [m g, divides, m ab, ref productDividesPropertyLabel]
            item $ do
                s [m g, divides, m c, ref coprimeCompoundPropertyLabel, ref coprimeDividesProductPropertyLabel]
            item $ do
                s [m g, "is the smallest", integer, "that does so"]
                newline
                let z = "z"
                s ["Suppose there was an", integer, m z, "that divided both", m ab, and, m c]
                let x = "x"
                    y = "y"
                s ["That would mean that there exist integers", m x, and, m y]
                ma $ z * x =: ab <> quad <> text and <> quad <> z * y =: c
                let t = "t"
                    u = "u"
                    v = "v"
                    w = "w"
                s ["According to", bezoutsLemma, ref bezoutsIdentityLemmaLabel <> ", there must exist", integers, csa [m t, m u, m v, m w], "as follows"]
                ma $ g =: (pars $ t * a + u * c) * (pars $ v * b + w * c)
                s ["Now observe the following"]
                aligneqs g
                    [ t * a * v * b + t * a * w * c + u * c * v * b + u * c * w * c
                    , z * x * t * v + z * y * t * a * w + z * y * u * v * b + z * y * u * c * w
                    , z * (pars $ x * t * v + y * t * a * w + y * u * v * b + y * u * c * w)
                    ]
                s ["We conclude that", m z, divides, m g]



gcdMultiplicativeConsequence :: Note
gcdMultiplicativeConsequence = con $ do
    lab gcdMultiplicativeConsequenceLabel
    let a = "a"
        b = "b"
        c = "c"
        bc = b * c
    s ["Let", csa [m a, m b, m c], be, integers, "such that", m a, and, m b, are, coprime]
    s [m a, and, m bc, are, coprime, "if and only if both", m a, and, m b <> ",", and, m a, and, m c, are, coprime]

    proof $ do
        s ["Proof of an equivalence"]
        itemize $ do
            item $ do
                s ["If", m $ a `copr` bc, "holds, then", m $ gcd a c * gcd b c, "must be one", ref gcdMultiplicativePropertyLabel]
                s ["Because they are", integers <> ", this means that both", m $ gcd a c, and, m $ gcd b c, "must be one and therefore, by definition,", m $ a `copr` c, and, m $ b `copr` c, "hold"]
            item $ do
                s ["If both", m $ a `copr` c, and, m $ b `copr` c, "hold, then the product of their", greatestCommonDivisors, "must be one and therefore", m a, and, m bc, coprime]



moduloS :: Note
moduloS = section "Modular arithmetic" $ do
    oddEvenDefinition
    modularIntegersDefinition
    solutionOfLinearCongruenceTheorem
    chineseRemainderTheoremPart
    quadraticResidueDefinition
    quadraticResidueExamples
    legendreSymbolDefinition
    legendreSymbolExamples
    jacobiSymbolDefinition
    jacobiSymbolExamples

modularIntegersDefinition :: Note
modularIntegersDefinition = de $ do
    let n = "n"
    s [the, integers, "modulo an", integer, m n, "are defined as the following", quotientGroup]
    ma $ intmod n === qgrp ints (n <> ints)
    let a = "a"
        b = "b"
        q = "q"

    s ["We say that an", integer, m a, is, congruent', with, "an", integer, m b, "modulo an", integer, m n, "if there exists an", integer, m q, "such that", m $ a =: b + q * n, "holds"]
    ma $ eqmod n a b === te (q ∈ ints) (a =: b + q * n)
    todo "fully formalize once we have a good chapter on groups"

oddEvenDefinition :: Note
oddEvenDefinition = de $ do
    s ["An", integer, "is called", odd', "if it is", congruent, with, m 1, modulo, m 2]
    s ["If it is instead", congruent, with, m 0, modulo, m 2 <> ", then we call it", even']

solutionOfLinearCongruenceTheorem :: Note
solutionOfLinearCongruenceTheorem = thm $ do
    lab solutionOfLinearCongruenceTheoremLabel
    let a = "a"
        n = "n"
        b = "b"
    s ["Let", csa [m a, m b, m n], be, integers]
    let x = "x"
    s ["There exists an", integer, m x, "as follows if and only if", m $ gcd a n, divides, m b]
    s [m b, "is unique if", m a, and, m n, are, coprime]
    ma $ (pars $ gcd a n .| b) ⇔ (pars $ te (x ∈ ints) $ eqmod n (a * x) b)

    proof $ do
        s ["Proof of an equivalence"]
        itemize $ do
            item $ do
                let y = "y"
                s ["If", m $ gcd a n, divides, m b, "then there exists an", integer, m y, "as follows"]
                ma $ gcd a n * y =: b
                let p = "p"
                    q = "q"
                s [bezoutsLemma, "tells us that there exist", integers, m p, and, m q, "as follows"]
                ma $ gcd a n =: a * p + n * q
                s ["If we substitute this in the above equation, we get the following"]
                ma $ a * p * y + n * q * y =: b
                s ["If we now look at the second term on the left-hand side, we see that it's divisible by", m n, "so it dissappears when viewed modulo", m n]
                ma $ eqmod n (a * p * y) b
                s ["We find that", m $ p * y, "is a valid candidate for", m x]
                newline
                let u = "u"
                s ["Now, assume", m a, and, m n, are, coprime, and, m u, "is another such", integer, "solution"]
                s ["If", m n, "equals", m 1 <> ", then", m x, "is trivially unique, because it's always zero"]
                s ["Otherwise, note that", m a, "cannot be zero because then the", greatestCommonDivisor, "of", m a, and, m n, "would be", m n, "instead of", m 1]
                ma $ eqmod n (a * x) (a * u)
                s ["We divide out", m a, "which we're allowed to do because", m a, "is not zero"]
                s ["We find that", m x, and, m u, "are equal and therefore", m x, "is unique"]

            item $ do
                s ["Let", m x, "be an", integer, "as follows"]
                ma $ eqmod n (a * x) b
                let f = "f"
                s ["This means that there exists an", integer, m f, "as follows"]
                ma $ a * x + f * n =: b
                let p = "p"
                    q = "q"
                    g = gcd a n
                s ["Now,", m $ gcd a n, divides, m a, and, m n, "so there exist", integers, m p, and, m q, "as follows"]
                ma $ g * p =: a <> qquad <> text and <> qquad <> g * q =: n
                s ["After substitution, we find the following"]
                ma $ g * p * x + g * q * f =: b
                s ["We conclude that", m g, divides, m b, with, quotient, m $ p * x + q * f]


chineseRemainderTheoremPart :: Note
chineseRemainderTheoremPart = thm $ do
    s [the, chineseRemainderTheorem']
    newline
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
        s ["Because the", integers, m ns, are, pairwiseCoprime <> ",", m nni, and, m ni, "are also", coprime, ref gcdMultiplicativeConsequenceLabel]
        ma $ gcd nni ni =: 1
        let x = "x"
            xi = x !: i
        s ["This means that the", linearCongruence, m $ eqmod nk (nni * xi) 1, "has some unique solution", m xi, ref solutionOfLinearCongruenceTheoremLabel]
        let ai = a !: i
        s ["Define", m $ x =: sumcmpr (i =: 1) k (ai * nni * xi)]
        s ["We will now prove that", m x, "satisfies all the", linearCongruences]
        s ["Let", m i, "therefore be arbitrary"]
        let j = "j"
            nj = n !: j
        s ["Note first that for any", m j, "different from", m i <> ",", m nj, divides, m nni]
        ma $ eqmod ni nj 0
        s ["We find that the following holds"]
        ma $ eqmod ni x (ai * nni * xi)
        s ["Finally, because", m $ nni * xi, "was found to be congruent with", m 1, "modulo", m ni, "we find that", m x, "is congruent with", m ai]
        newline
        s ["Now we only have to prove that this solution is unique modulo", m n]
        let y = "y"
        s ["Suppose that", m y, "was another solution of the system"]
        s ["This means that each", m ni, divides, m $ y - x, "but because each of the moduli are", coprime, "we find that also", m nn, divides, m $ y - x, ref coprimeDividesProductPropertyLabel]
        s ["That is,", m y, and, m x, are, congruent, modulo, m nn]



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
            ((raw "n\\setminus q") : P.map rawn [1 .. n])
            ( P.map (\i -> do
                rawn i : (P.map (\j -> if j P.< (i P.+ 1) then (rawn $ j P.^ (2 :: P.Int) `P.mod` i) else mempty) [1 .. n])
                ) [0 .. n])



legendreSymbolDefinition :: Note
legendreSymbolDefinition = de $ do
    let a = "a"
        p = "p"
    s ["Let", m a, "be an", integer, and, m p, "an", odd, prime]
    s [the, legendreSymbol', "of", m a, over, m p, "is defined as follows"]
    ma $ (leg a p ===) $ cases $ do
        1 & text "if " <> m a <> text (" is a " <> quadraticResidue <> " " <> modulo <> " ") <> m p <> text " and " <> neg (p .| a)
        lnbk
        (-1) & text "if " <> m a <> text (" is not a " <> quadraticResidue <> " " <> modulo <> " ") <> m p
        lnbk
        0 & text "if " <> p .| a

legendreSymbolExamples :: Note
legendreSymbolExamples = do
    ex $ do
        s ["Note that", m $ 4 ^ 2 =: 16, and, m $ eqmod 11 16 5]
        ma $ leg 5 11 =: 1
    ex $ do
        ma $ leg 6 11 =: -1


jacobiSymbolDefinition :: Note
jacobiSymbolDefinition = de $ do
    let a = "a"
        n = "n"
    s ["Let", m a, "be an", integer, and, m n, "an", odd, naturalNumber, "with the following", primeFactorization]
    let p = "p"
        t = "t"
        (p1, p2, pt, _) = buildList p t
        v = "v"
        (v1, v2, vt, _) = buildList v t
        i = "i"
        pi = p !: i
        vi = v !: i
    let (^) = (.^:)
    ma $ n =: p1 ^ v1 * p2 ^ v2 * dotsb * pt ^ vt =: prodcmpr (i =: 1) t (pi ^ vi)
    s [the, jacobiSymbol', "of", m a, over, m p, "is defined as follows"]
    ma $ jac a n === (leg a p1) ^ v1 * (leg a p2) ^ v2 * dotsb * (leg a pt) ^ vt =: prodcmpr (i =: 1) t ((leg a pi) ^ vi)


jacobiSymbolExamples :: Note
jacobiSymbolExamples = do
    let (^) = (.^:)
    ex $ do
        ma $ jac 5 9 =: jac 5 (3 ^ 2) =: (leg 5 3) ^ 2 =: 1
    ex $ do
        ma $ jac 5 12 =: jac 5 (3 * 2 ^ 2) =: (leg 5 3) * (leg 5 2) ^ 2 =: -1








