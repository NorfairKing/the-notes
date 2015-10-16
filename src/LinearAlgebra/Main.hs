module LinearAlgebra.Main where

import           Notes

import           LinearAlgebra.InproductSpaces (inproductSpaces)
import           LinearAlgebra.VectorSpaces    (vectorSpaces)

linearAlgebra :: Notes
linearAlgebra = notes "linear-algebra"
  [
    notesPart "header" (chapter "Linear Algebra")
  , vectorSpaces
  , inproductSpaces
  ]
