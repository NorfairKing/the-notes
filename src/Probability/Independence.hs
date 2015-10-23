module Probability.Independence (
    independence
  ) where

import           Notes

independence :: Notes
independence = notesPart "independence" body

psDec :: Note
psDec = s ["Let ", m prsp, " be a ", ix "probability space"]

body :: Note
body = do
  section "Independence"
  independenceDefinition
  dependenceDefinition
  conditionalProbabilityIndependentEvents
  pairwiseIndependenceDefinition
  mutualIndependenceDefinition
  mutualIndependenceImpliesPairwiseIndependence
  infiniteMutalIndependenceDefinition

independent :: Note
independent = ix "independent"

independenceDefinition :: Note
independenceDefinition = de $ do
  psDec
  s ["Two events ", m a, and, m b, " in ", m prsa, " are called ", term "independent", " if the following equality holds"]
  ma $ prob (a ∩ b) =: prob a * prob b

  where
    a = "A"
    b = "B"

dependenceDefinition :: Note
dependenceDefinition = de $ do
  psDec
  s ["If two events ", m a, and, m b, " in ", m prsa, " are not ", independent, ", they are called ", term "dependent", " events"]
  s ["This depedence is called.."]
  itemize $ do
    item $ s [term "positive dependence", " if ", m (prob (a ∩ b) > prob a * prob b), " holds"]
    item $ s [term "negative dependence", " if ", m (prob (a ∩ b) < prob a * prob b), " holds"]

  where
    a = "A"
    b = "B"

conditionalProbabilityIndependentEvents :: Note
conditionalProbabilityIndependentEvents = thm $ do
  psDec
  s ["Let ", m a, and, m b, " be two ", independent, " events in ", m prsa]
  ma $ cprob a b =: prob a

  proof $ do
    ma $ cprob a b =: prob (a ∩ b) /: prob b =: (prob a * prob b) /: prob b =: prob a

  where
    a = "A"
    b = "B"

pairwiseIndependenceDefinition :: Note
pairwiseIndependenceDefinition = de $ do
  s ["A set of events is called ", term "pairwise independent", " if every two events in the set are independent"]

mutualIndependenceDefinition :: Note
mutualIndependenceDefinition = de $ do
  psDec
  s ["A set ", m x, " of events is called ", term "mutual independence", " if the following holds"]
  ma $ fa (y ∈ powset x) $ prob (setincmp (a ∈ y) a) =: prodcmp (a ∈ y) (prob a)
  where
    a = "A"
    x = "X"
    y = "Y"

mutualIndependenceImpliesPairwiseIndependence :: Note
mutualIndependenceImpliesPairwiseIndependence = thm $ do
  s ["Mutual independence implies pairwise independence"]
  noproof

infiniteMutalIndependenceDefinition :: Note
infiniteMutalIndependenceDefinition = de $ do
  s ["An infinite set of events is called mutually independent if every finite subset is mutually independent"]




