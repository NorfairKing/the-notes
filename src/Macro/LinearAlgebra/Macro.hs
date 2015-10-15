module Macro.LinearAlgebra.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro


-- Transpose
trans :: Note -> Note
trans n = n ^: "T"

veclst :: Note -> Note -> Note
veclst m n = pars $ m <> ", " <> dotsc <> ", " <> n

veclist :: Note -> Note -> Note -> Note
veclist m n o = pars $ m <> ", " <> n <> ", " <> dotsc <> ", " <> o

-- Matrix inverse
matinv :: Note -> Note
matinv mat = mat ^: (-1)

-- Linear Algebra Set
laset :: Note
laset = "V"

-- Linear Algebra Field
lafield :: Note
lafield = "F"

-- Linear Algebra Field Addition
lafadd :: Note
lafadd = comm0 "star"

(+.) :: Note -> Note -> Note
(+.) = binop lafadd

-- Linear Algebra Field Multiplication
lafmul :: Note
lafmul = comm0 "ast"

(*.) :: Note -> Note -> Note
(*.) = binop lafmul

-- Linear Algebra Vector Space Addition
laadd :: Note
laadd = "+"

(<+>) :: Note -> Note -> Note
(<+>) = binop laadd

-- Linear Algebra Vector Space Scalar Multiplication
lamul :: Note
lamul = comm0 "cdot"

(<*>) :: Note -> Note -> Note
(<*>) = binop lamul


-- Linear Algebra Vector Space
lavs :: Note
lavs = lavs_ lafield laset laadd lamul

lavs_ :: Note -- Field
      -> Note -- Set
      -> Note -- Addition
      -> Note -- Multiplication
      -> Note
lavs_ f s a m = quadruple f s a m
