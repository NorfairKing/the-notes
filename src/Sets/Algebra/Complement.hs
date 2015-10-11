module Sets.Algebra.Complement (setComplement, complement) where

import           Notes

complement :: Note
complement = ix "complement"

setComplement :: Notes
setComplement = notesPart "complement" body

body :: Note
body = do
  subsection "Set complement"
  complementDefinition

a, b, x, y :: Note
a = "A"
b = "B"
c = "C"
x = "x"
y = "y"

complementDefinition :: Note
complementDefinition = de $ do
  s ["The ", term "comlement", " of a set ", m a, " relative to a set ", m b, " is the set of all elements of ", m b, " that are not in ", m a, "."]


