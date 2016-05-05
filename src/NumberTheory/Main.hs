module NumberTheory.Main where

import           Notes

import           Functions.Basics.Macro
import           Functions.BinaryOperation.Terms
import           Functions.Jections.Terms
import           Relations.Equivalence.Macro
import           Relations.Equivalence.Terms
import           Sets.Basics.Terms

import           NumberTheory.Macro
import           NumberTheory.Terms

numberTheoryC :: Note
numberTheoryC = chapter "Number Theory" $ do
    naturalNumbersS
    wholeNumbersS

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


wholeNumbersDefinition :: Note
wholeNumbersDefinition = de $ do
    s [wholeNumbers', or, integers', m ints, "are defined as the", equivalenceClasses, "of", m $ naturals ^ 2, "with respect to the following", equivalenceRelation]
    let (a, b, c, d) = ("a", "b", "c", "d")
    -- b - a = d - c
    ma $ tuple a b .~ tuple c d === b + c =: d + a
    nte $ do
        s ["Intuitively, an", element, m $ tuple a b, "represents", m $ b - a, "even if that", element, "does not exist in", m nats]

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
    ma $ func i nats ints a $ tuple 0 a







