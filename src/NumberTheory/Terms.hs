module NumberTheory.Terms where

import           Notes

makeDefs
    [ "natural number"
    , "addition"
    , "subtraction"
    , "multiplication"
    , "division"
    , "whole number"
    , "integer"
    , "divisible"
    , "divisor"
    , "divides"
    , "quotient"
    , "greatest common divisor"
    , "least common multiple"
    , "coprime"
    , "relatively prime"
    , "mutually prime"
    , "prime"
    , "Bezout's Lemma"
    , "pairwise coprime"
    , "prime factorization"
    , "congruent"
    , "odd"
    , "even"
    , "modulo"
    , "linear congruence"
    , "Chinese remainder theorem"
    , "quadratic residue"
    , "Legendre symbol"
    , "Euler's criterion"
    , "Jacobi symbol"
    ]

makeProps
    [ "divides transitive"
    , "divides multiples"
    , "product divides"
    , "coprime division cancels"
    , "coprime divides product"
    , "coprime compound"
    , "gcd multiplicative"
    ]

makeThms
    [ "Solution of linear congruence"
    , "Chinese remainder"
    , "Euler criterion"
    ]

makeLems
    [ "Bezouts identity"
    ]

makeCons
    [ "gcd multiplicative"
    ]
