module Macro.LinearAlgebra.Macro where

import           Types

import           Macro.Numbers.Macro

import           Macro.Math
import           Macro.MetaMacro
import           Macro.Text
import           Macro.Tuple


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

-- Real vectors
realVecSpace :: Note -> Note
realVecSpace p = reals ^: p

-- Operations on Vector of numbers
realVecAddition :: Note
realVecAddition = addition

realVecScalarMultiplication :: Note
realVecScalarMultiplication = multiplication

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
laadd = bm "+"

(<+>) :: Note -> Note -> Note
(<+>) = binop laadd

-- Linear Algebra Vector Space Scalar Multiplication
lamul :: Note
lamul = bm $ comm0 "cdot"

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
lavs_ = quadruple

realVectorsSpace :: Note -> Note
realVectorsSpace p = lavs_ reals (reals ^: p) "+" (comm0 "cdot")


-- Linear Algebra Inproduct
lainprod :: Note
lainprod = autoBrackets langle rangle $ cs [comm0 "cdot", comm0 "cdot"]

lain :: Note -> Note -> Note
lain v w = autoBrackets langle rangle $ cs [v, w]

(<.>) :: Note -> Note -> Note
(<.>) = lain

realVectorInproduct :: Note
realVectorInproduct = lainprod

-- | Dotproduct
(/.\) :: Note -> Note -> Note
(/.\) = binop $ negsp <> comm0 "cdot" <> negsp
  where negsp = commS "kern" <> raw "-2px"

-- | Addition of euclidean vectors
(/+\) :: Note -> Note -> Note
(/+\) = (<+>)


-- Linear Algebra Inner Product Space
laips :: Note
laips = laips_ lafield laset laadd lamul lainprod

laips_ :: Note -- Field
       -> Note -- Set
       -> Note -- Addition
       -> Note -- Multiplication
       -> Note -- Inner product
       -> Note
laips_ = quintuple

euclideanInnerProductSpace :: Note -> Note
euclideanInnerProductSpace p = laips_ reals (reals ^: p) realVecAddition realVecScalarMultiplication lainprod

