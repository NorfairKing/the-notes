module Macro.Temp where

import           Types

import           Macro.Index

leastSignificantBit :: Note
leastSignificantBit = ix "least significant bit"

base :: Note
base = ix "base"

infinite :: Note
infinite = ix "infinite"

differentiable :: Note
differentiable = ix "differentiable"

localMinimum :: Note
localMinimum = ix "local minimum"

localMaximum :: Note
localMaximum = ix "local maximum"

derivative :: Note
derivative = ix "derivative"

homogenous :: Note
homogenous = ix "homogenous"

basis :: Note
basis = ix "basis"

matrix :: Note
matrix = ix "matrix"

additive :: Note
additive = ix "additive"

invertible :: Note
invertible = ix "invertible"

sum :: Note
sum = ix "sum"

product :: Note
product = ix "product"

increasing :: Note
increasing = ix "increasing"

decreasing :: Note
decreasing = ix "decreasing"

rightCongruent :: Note
rightCongruent = ix "right congruent"

leftCongruent :: Note
leftCongruent = ix "left congruent"

constant :: Note
constant = ix "constant"

constants :: Note
constants = ix_ "constant" "constants"

-- Matrix pseudo inverse
pseudoInverse :: Note
pseudoInverse = ix "pseudo inverse"

commutative :: Note
commutative = ix "commutative"

idempotent :: Note
idempotent = ix "idempotent"

distributive :: Note
distributive = ix "distributive"

sequence :: Note
sequence = ix "sequence"

finite :: Note
finite = ix "finite"

-- Matrix inverse
inverse :: Note
inverse = ix "inverse"

objectiveFunction :: Note
objectiveFunction = ix "objective function"

gradient :: Note
gradient = ix "gradient"

subgradient :: Note
subgradient = ix "subgradient"

subgradients :: Note
subgradients = ix_ "subgradients" "subgradient"

projection :: Note
projection = ix "projection"

closed :: Note
closed = ix "closed"

transformation :: Note
transformation = ix "transformation"

directed :: Note
directed = ix "directed"

acyclic :: Note
acyclic = ix "acyclic"

permutation :: Note
permutation = ix "permutation"

permutations :: Note
permutations = ix "permutations"

countable :: Note
countable = ix "countable"

smallest :: Note
smallest = ix "smallest"

-- Groups
cyclic :: Note
cyclic = ix "cyclic"

-- * Number theory

relativelyPrime_ :: Note
relativelyPrime_ = ix "relatively prime"

primes :: Note
primes = ix "primes"

chineseRemainderTheorem_ :: Note
chineseRemainderTheorem_ = ix "Chinese remainder theorem"
