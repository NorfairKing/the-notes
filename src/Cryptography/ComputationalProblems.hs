module Cryptography.ComputationalProblems where

import           Notes                                    hiding (cyclic,
                                                           inverse)

import           Groups.Macro
import           Groups.Terms
import           Rings.Macro
import           Rings.Terms
import           Sets.Basics.Terms

-- import           Cryptography.ComputationalProblems.Macro
import           Cryptography.ComputationalProblems.Terms

computationalProblemsS :: Note
computationalProblemsS = section "Computational Problems" $ do
        discreteLogarithmProblemDefinition
        additiveDLEasy
        dlReducable
        dlModTwoInEvenOrderGroup
        computationalDHProblemDefinition
        diffieHellmanTripleDefinition
        decisionalDHProblemDefinition


discreteLogarithmProblemDefinition :: Note
discreteLogarithmProblemDefinition = de $ do
    lab discreteLogarithmDefinitionLabel
    lab dLDefinitionLabel
    let aa = "A"
        a = "a"
        g = "g"
    s [the, discreteLogarithm', "(" <> dL' <> ")", "problem", "for a", cyclic_, group, m $ grp_ =: grp (genby g) grpop_, "is the problem of computing, for a given", group, element, m $ aa ∈ grps_, "the exponent", m $ integer a, " such that", m $ aa =: g ^ a, "holds"]

additiveDLEasy :: Note
additiveDLEasy = thm $ do
    let n = "n"
    s [the, discreteLogarithm, "problem is trivially solvable in the", group, m $ intagrp n]
    proof $ do
        let z = "z"
            a = "a"
            g = "g"
        s ["Recall that, for any element", m (z ∈ intmod n) <> ", we are looking for the integer", m $ integer a, "such that", m $ z =: g * a, "where", m g, "is a", generator, "of", m $ intagrp n]
        s ["Luckily, ", m $ intagrp n, "gives rise to a", ring, m $ intring n, "as well"]
        s ["This allows us to find", m a, "by dividing", m z, by, m g]
        s ["More precicely: because", m g, "is a", generator, "means that", m g, "must have a multiplicative inverse in", m $ intring n, "otherwise no multiple of", m g, "would be equal to", m 1]
        s ["Now the only thing we need to do is go through the", elements, "of", m $ intmod n, "multiply each of them by", m g, "in", m $ intring n, "and check if the result equals", m 1, "to find the multiplicative inverse", m $ rinv g, "of", m g, "in", m $ intring n]
        s ["We then compute", m a, "by evaluating", m $ rinv g * z =: rinv g * g * a =: a]
        s ["We could also use the extended Euclidean algorithm to find", m $ rinv g, "even more efficiently"]
        refneeded "Extended Euclidean algorithm"

dlReducable :: Note
dlReducable = thm $ do
    let g = "g"
        h = "h"
    s [the, discreteLogarithm, "problem in a", group, m grp_, "for a", generator, m g, "is reducable to the", discreteLogarithm, "problem in that same", group, "but for a different", generator]

    proof $ do
        let a = "A"
        s ["Let", m a, "be an algorithm that solves the", discreteLogarithm, "problem for a", generator, m g]
        s ["We construct an algorithm that solves the", discreteLogarithm, "problem for another", generator, m h, "of", m grp_, "as follows"]
        let z = "z"
            b = "b"
            c = "c"
        s ["Let", m z, "be the", group, element, "that we want the", discreteLogarithm, m b, "base", m h, "in", m grp_, "of"]
        s ["There then exists a", m $ integer c, "such that", m c, "is the", discreteLogarithm, "base", m g, "in", m grp_, "of", m z]
        ma $ z =: h ^ b =: g ^ c
        let d = "d"
        s ["Because", m h, "is an", element, "of", m grps_ <> ",", "there exists a", m $ integer d, "such that", m $ h =: g ^ d, "holds"]
        ma $ z =: (pars $ g ^ d) ^ b =: g ^ c
        s ["This means that we have the following equation for", m c, "in", m $ intring $ ord grps_]
        ma $ d * b =: c
        s ["The algorithm now uses", m a, "to find", m c, from, m z, and, m d, from, m h]
        s ["It then computes the multiplicative inverse of", m d, "in", m $ intring $ ord grps_, "with the extended Euclidean algorithm and finally computes", m b, "by evaluating", m $ rinv d * c =: rinv d * d * b =: b]

dlModTwoInEvenOrderGroup :: Note
dlModTwoInEvenOrderGroup = thm $ do
    let n = "n"
    s ["Let", m grp_, beA, group, with, "an even", order, m $ ord grp_ =: 2 * n]
    s ["There exists an efficient algorithm to compute whether the", discreteLogarithm, "of an", element, "is even or not"]

    proof $ do
        let x = "x"
        s ["Let", m x, beAn, element, "of", m grps_]
        let g = "g"
            a = "a"
        s ["For a given base", m g, "the task is to compute", m $ a `mod` 2, "such that", m $ x =: g ^ a, "holds"]
        let q = "q"
            r = "r"
        s ["Define", m q, and, m r, "as the quotient and rest after division by", m 2, "of", m a]
        s ["Observe first the following"]
        ma $ x ^ n =: g ^ (a * n) =: g ^ ((pars $ 2 * q + r) * n) =: g ^ (2 * n * q) ** (g ^ (r * n) =: g ^ (r * n))
        s ["This means that", m $ x ^ n, "will be equal to the", neutralElement, "if", m a, "is even and", m $ g ^ n, "(which cannot be the", neutralElement <> ") if", m a, "is odd"]
        s ["We only have to compare", m $ x ^ n, "to the", neutralElement, "to determine", m $ a `mod` 2]


computationalDHProblemDefinition :: Note
computationalDHProblemDefinition = de $ do
    lab computationalDiffieHellmanDefinitionLabel
    lab cDHDefinitionLabel
    let a = "a"
        b = "b"
        g = "g"
    s [the, computationalDiffieHellman, "(" <> cDH' <> ")", "problem for a given", cyclic, group, m $ grp_ =: grp (genby g) grpop_, "is the problem of computing, for given group elements", m $ g ^ a, and, m $ g ^ b, "the group element", m $ g ^ (a * b)]

diffieHellmanTripleDefinition :: Note
diffieHellmanTripleDefinition = de $ do
    lab diffieHellmanTripleDefinitionLabel
    let a = "a"
        b = "b"
        c = "c"
        g = "g"
    s ["A", diffieHellmanTriple, "in a given", cyclic, group, m $ grp_ =: grp (genby g) grpop_, "is a triple of the form", m $ triple (g ^ a) (g ^ b) (g ^ (a * b)), "where", m a <> ",", m b, and, m c, "are hole numbers"]


decisionalDHProblemDefinition :: Note
decisionalDHProblemDefinition = de $ do
    lab computationalDiffieHellmanDefinitionLabel
    lab cDHDefinitionLabel
    let a = "a"
        b = "b"
        c = "c"
        g = "g"
    s [the, decisionalDiffieHellman', "(" <> dDH' <> ")", "problem for a given", cyclic, group, m $ grp_ =: grp (genby g) grpop_, "is the problem of determining whether, for given group elements", (m $ g ^ a) <> ",", m $ g ^ b, and, m $ g ^ c, "whether they are chosen randomly and independently from", m grps_, "or form a", diffieHellmanTriple]



