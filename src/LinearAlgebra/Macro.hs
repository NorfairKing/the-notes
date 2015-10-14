module LinearAlgebra.Macro where

import           Macro.Math
import           Types

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
