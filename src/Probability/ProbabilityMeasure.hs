module Probability.ProbabilityMeasure (probabilityMeasure) where

import           Notes

probabilityMeasure :: Notes
probabilityMeasure = notesPart "probability-measure" body

body :: Note
body = do
  section "Probability Measures"
  probabilityMeasureDefinition
  measurablespaceDefinition


msDec :: Note
msDec = s ["Let ", m prms, " be a ", ix "measurable space", "."]

probabilityMeasureDefinitionLabel :: Note
probabilityMeasureDefinitionLabel = "de:probability-measure"

probabilityMeasureDefinition :: Note
probabilityMeasureDefinition = de $ do
  msDec
  s ["A ", term "probability measure", " is a function ", m prpm, " with the following three properties: "]
  ma $ fun prpm prsa $ ccint 0 1

  enumerate $ do
    item $ m $ (prob pruniv) =: 1
    item $ m $ fa ("A" ∈ prsa) ((prob "A") >=: 0)
    item $ do
      term "countable additivity"
      newline
      s ["Let ", m (sequ an "n"), " be a countably infinite ", ix "sequence", " of pairwise disjunct sets."]
      ma $ prob (setuncmp (natural "n") an) =: sumcmp (natural "n") (prob an)

  where an = "A" !: "n"

msppsDec :: Note
msppsDec = s ["Let ", m prms, " be a ", ix "measurable space", " and ", m prpm, " a ", ix "probability measure", "."]

measurablespaceDefinition :: Note
measurablespaceDefinition = de $ do
  msppsDec
  m prsp
  " is called a "
  term "probability space"
