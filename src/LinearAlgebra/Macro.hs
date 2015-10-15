module LinearAlgebra.Macro where

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

-- Linear Algebraa Vector Space Addition
laadd :: Note
laadd = "+"

(<+>) :: Note -> Note -> Note
(<+>) = binop laadd

-- Linear Algebraa Vector Space Multiplication
lamul :: Note
lamul = comm0 "cdot"

(<*>) :: Note -> Note -> Note
(<*>) = binop lamul



-- Linear Algebra Vector Space
-- lavs :: Note
-- lavs = "ddd
