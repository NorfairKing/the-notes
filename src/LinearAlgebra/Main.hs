module LinearAlgebra.Main where

import           Notes

linearAlgebra :: Notes
linearAlgebra = notes "linear-algebra"
  [
    notesPart "header" (chapter "Linear Algebra")
  , notesPart "vector-spaces" vectorSpaces
  ]


vectorSpaces :: Note
vectorSpaces = do
  vectorSpaceDefinition

vectorSpaceDefinition :: Note
vectorSpaceDefinition = de $ do
  s ["Let ", m lafield, " be a field an let ", m laset, " be a set"]
  s ["Let ", m (pars laadd), " be an internal binary operation on ", m laset]
  s ["Let ", m (pars lamul), " be a binary operation"]
  ma $ fun (pars lamul) (lafield ⨯ laset) laset
