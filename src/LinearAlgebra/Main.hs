module LinearAlgebra.Main where

import           Notes

import           LinearAlgebra.InproductSpaces
import           LinearAlgebra.VectorSpaces

linearAlgebra :: Note
linearAlgebra = chapter "Linear Algebra" $ do
    vectorSpaces
    inproductSpaces
