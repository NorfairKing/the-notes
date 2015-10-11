module Sets.Algebra.Difference (setDifference, difference) where

import           Notes

difference :: Note
difference = ix "difference"

setDifference :: Notes
setDifference = notesPart "difference" body

body :: Note
body = do
  subsection "Set difference"

