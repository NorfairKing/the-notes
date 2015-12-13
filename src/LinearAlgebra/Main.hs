module LinearAlgebra.Main where

import           Notes

import           LinearAlgebra.InproductSpaces (inproductSpaces)
import           LinearAlgebra.VectorSpaces    (vectorSpaces)

linearAlgebra :: Note
linearAlgebra = note  "linear-algebra" $ do
    chapter "Linear Algebra"
    vectorSpaces
    inproductSpaces
