module NumberTheory.Main where

import           Notes

import           Functions.Basics.Macro
import           Functions.BinaryOperation.Terms
import           Functions.Jections.Terms
import           Groups.Macro
import           Groups.Terms
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

divisibilityDefinition :: Note
divisibilityDefinition = de $ do
    todo "define divisibility more abstractly in integrity domains"
    let a = "a"
    let b = "b"
    let c = "c"
    s ["We define a", wholeNumber, m a, "to be", divisible', "by another", wholeNumber, m b, "if there exists a", wholeNumber, m c, "such that", m $ a `divZ` b =: c]

moduloS :: Note
moduloS = do
    modularIntegersDefinition
    quadraticResidueDefinition

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
        x = "x"
        y = "y"
    s ["A", quadraticResidue', "modulo an", integer, m n, "is an", integer, m x, "such that there exists an", integer, m y, "as follows"]
    ma $ eqmod n (y ^ 2) x


