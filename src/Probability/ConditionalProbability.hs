module Probability.ConditionalProbability (
    conditionalProbability

  , conditionalProbabilityDefinitionLabel
  ) where

import           Notes

conditionalProbability :: Notes
conditionalProbability = notesPart "conditional-probability" body

body :: Note
body = do
  conditionalProbabilityDefinition
  conditionalProbabilityEventGivenItself
  conditionalProbabilityEventGivenUniverse

conditionalProbabilityDefinitionLabel :: Label
conditionalProbabilityDefinitionLabel = delab "conditional-probability"

event :: Note
event = ix "event"

a,b,ai :: Note
a = "A"
b = "B"
ai = a ∈ prsa

conditionalProbabilityDefinition :: Note
conditionalProbabilityDefinition = de $ do
  lab conditionalProbabilityDefinitionLabel

  s ["The", term "conditional probability", " of an ", event, m (a ∈ prsa), " given an ", event, m (b ∈ prsa), " with ", m (prob b /=: 0), " is denoted as ", m (cprob a b), ""]
  ma $ cprob a b === (prob (a ∩ b) /: prob b)

psDec :: Note
psDec = s ["Let ", m prsp, " be a ", ix "probability space", ""]

conditionalProbabilityEventGivenItself :: Note
conditionalProbabilityEventGivenItself = prop $ do
  psDec
  ma $ fa ai $ cprob a a =: 1
  proof $ ma $ fa ai $ cprob a a =: (prob (a ∩ a) /: prob a) =: (prob a /: prob a) =: 1

conditionalProbabilityEventGivenUniverse :: Note
conditionalProbabilityEventGivenUniverse = prop $ do
  psDec
  ma $ fa ai $ cprob a pruniv =: prob a
  "We say that every event is independent of the universe."

  proof $ ma $ fa ai $ cprob a pruniv =: (prob (a ∩ pruniv) /: prob pruniv) =: (prob a /: prob pruniv) =: (prob a /: 1) =: prob a
