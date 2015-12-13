module Probability.ProbabilityMeasure (
  probabilityMeasure

  ) where

import           Notes
import           Sets.Algebra.Main      (setDifferenceEquivalentDefinitionLabel,
                                         unionComplementaryLawLabel)
import           Sets.Basics            (universalSetSupsetOfAllSetsLabel)

import           Functions.Basics.Macro

probabilityMeasure :: Note
probabilityMeasure = note "probability-measure" body

body :: Note
body = do
  section "Probability Measures"
  probabilityMeasureDefinition
  measurablespaceDefinition
  probabilityMeasureFiniteAdditivity
  probabilitySpaceProbabilityOfComplement
  probabilityPartitionByIntersection
  probabilityOfUnion
  probabilityOfDifference
  probabilitySubsetImpliesSmaller
  probabilityAtMostOne

  traditionalProbabilityMeasures

traditionalProbabilityMeasures :: Note
traditionalProbabilityMeasures = do
  subsection "Traditional Probability Measures"
  uniformeProbabilityMeasure
  discreteProbabilityMeasure


msDec :: Note
msDec = s ["Let ", m prms, " be a ", ix "measurable space"]

probabilityMeasureDefinitionLabel :: Label
probabilityMeasureDefinitionLabel = delab "probability-measure"

probabilityMeasureDefinition :: Note
probabilityMeasureDefinition = de $ do
  lab probabilityMeasureDefinitionLabel

  msDec
  s ["A ", term "probability measure", " is a function ", m prpm, " with the following three properties:"]
  ma $ fun prpm prsa $ ccint 0 1

  enumerate $ do
    item $ m $ (prob pruniv) =: 1
    item $ m $ fa ("A" ∈ prsa) ((prob "A") >=: 0)
    item $ do
      term "countable additivity"
      newline
      s ["Let ", m (sequ an "n"), " be a countably infinite ", ix "sequence", " of pairwise disjunct sets"]
      ma $ prob (setuncmp (natural "n") an) =: sumcmp (natural "n") (prob an)

  s [m (prob a), " is called the ", term "probability", " that ", m a, " happens"]
  where
    a = "A"
    an = "A" !: "n"

msppsDec :: Note
msppsDec = s ["Let ", m prms, " be a ", ix "measurable space", " and ", m prpm, " a ", ix "probability measure"]

measurablespaceDefinition :: Note
measurablespaceDefinition = de $ do
  msppsDec
  m prsp
  " is called a "
  term "probability space"

probabilityMeasureFiniteAdditivityLabel :: Label
probabilityMeasureFiniteAdditivityLabel = thmlab "probability-measure-finite-additivity"

probabilityMeasureFiniteAdditivity :: Note
probabilityMeasureFiniteAdditivity = thm $ do
  lab probabilityMeasureFiniteAdditivityLabel

  s ["Let ", m prsp, " be a ", ix "probability space", " and let ", m (setcmpr an $ "n" ∈ setlst "1" "N"), " be ", m "N", " pairwise disjunct events of ", m prsa]
  ma $ prob (setuncmpr (n =: 1) "N" an) =: sumcmpr (n =: 1) "N" (prob an)

  proof $ s ["Use the ", ix "countable additivity", " property of probability measures", ref probabilityMeasureDefinitionLabel, " where only ", m n, " sets are non-empty"]
  where
    n = "n"
    an = "A" !: n

psDec :: Note
psDec = s ["Let ", m prsp, " be a ", ix "probability space"]

probabilitySpaceProbabilityOfComplement :: Note
probabilitySpaceProbabilityOfComplement = thm $ do
  psDec
  ma $ fa (a ∈ prsa) (prob (setc a) =: (1 - prob a))

  proof $ do
    s ["Let ", m a, " be an event in ", m prsa]
    s ["The union of ", m a, " and its complement is ", m pruniv, ".", ref unionComplementaryLawLabel]
    align_
      [
        pruniv & seteqsign <> (a ∪ setc a)
      , prob pruniv & "" =: prob (a ∪ setc a)
      , 1 & "" =: prob a + prob (setc a)
      , prob (setc a) & "" =: 1 - prob a
      ]

    "Notice that the second equivalence only holds because of the finite additivity propertiy of probability measures."
    ref probabilityMeasureFiniteAdditivityLabel

  con $ m $ prob emptyset =: 0

  where a = "A"

probabilityPartitionByIntersectionLabel :: Label
probabilityPartitionByIntersectionLabel = proplab "probability-partion-by-intersection"

probabilityPartitionByIntersection :: Note
probabilityPartitionByIntersection = prop $ do
  lab probabilityPartitionByIntersectionLabel

  psDec
  ma $ fa (a <> ", " <> b ∈ prsa) (prob b =: prob (b ∩ a) + prob (b ∩ setc a))

  proof $ do
    s ["Because ", m (b ∩ a), " and ", m (b ∩ setc a), " are disjunct, the theorem follows from the finite additivity property of probability measures"]
    ref probabilityMeasureFiniteAdditivityLabel

  where
    a = "A"
    b = "B"

probabilityOfUnionLabel :: Label
probabilityOfUnionLabel = proplab "probability-set-union"

probabilityOfUnion :: Note
probabilityOfUnion = prop $ do
  lab probabilityOfUnionLabel

  psDec
  ma $ fa (a <> ", " <> b ∈ prsa) (prob (a ∪ b) =: prob a + prob b - prob (a ∩ b))

  proof $ do
    s ["Let ", m a, " and ", m b, " be events in ", m prsa]
    align_
      [
        prob (a ∪ b) & "" =: prob (pars (a ∩ setc b) ∪ pars (a ∩ b) ∪ pars (setc a ∩ b))
      ,           "" & "" =: prob (a ∩ setc b) + prob (a ∩ b) + prob (setc a ∩ b)
      ,           "" & "" =: prob (a ∩ setc b) + prob (a ∩ b) + prob (setc a ∩ b) + pars (prob (a ∩ b) - prob (a ∩ b))
      ,           "" & "" =: pars (prob (a ∩ setc b) + prob (a ∩ b)) + pars (prob (setc a ∩ b) + prob (a ∩ b)) - prob (a ∩ b)
      ,           "" & "" =: prob a + prob b - prob (a ∩ b) ]
    "Note that we used the previous property in the last equation."
    ref probabilityPartitionByIntersectionLabel
  where
    a = "A"
    b = "B"

probabilityOfDifferenceLabel :: Label
probabilityOfDifferenceLabel = proplab "probability-set-difference"

probabilityOfDifference :: Note
probabilityOfDifference = prop $ do
  lab probabilityOfDifferenceLabel

  psDec
  ma $ fa (a <> ", " <> b ∈ prsa) (prob (a `setdiff` b) =: prob (a ∪ b) - prob b)

  proof $ do
    s ["Let ", m a, " and ", m b, " be events in ", m prsa]
    ma $ prob (a ∪ b) =: prob (b `setdiff` pars (b ∩ setc a)) =: prob b + prob (a `setdiff` b)
    "Note that we used the equivalent definition of set difference in the first equation."
    ref setDifferenceEquivalentDefinitionLabel
  where
    a = "A"
    b = "B"

probabilitySubsetImpliesSmallerLabel :: Label
probabilitySubsetImpliesSmallerLabel = proplab "probability-subset-implies-smaller-probability"

probabilitySubsetImpliesSmaller :: Note
probabilitySubsetImpliesSmaller = prop $ do
  lab probabilitySubsetImpliesSmallerLabel

  psDec
  ma $ fa (a <> ", " <> b ∈ prsa) ((a ⊆ b) ⇒ (prob a <= prob b))

  proof $ do
    ma $ prob a =: prob (b `setdiff` pars (b ∩ a)) =: prob b - prob (b ∩ a) <= prob b

    s ["Note that in the first equation we used that ", m a, " is a subset of ", m b, " and in the second equation, we used the previous property"]
    ref probabilityOfDifferenceLabel
  where
    a = "A"
    b = "B"


probabilityAtMostOne :: Note
probabilityAtMostOne = prop $ do
  psDec

  ma $ fa (a ∈ prsa) (prob a <= 1)
  proof $ do
    s ["Every set ", m a, " is a subset of ", m pruniv, ref universalSetSupsetOfAllSetsLabel]
    s [" so ", m (prob a), " must be smaller than ", m (prob pruniv =: 1), ref probabilityMeasureDefinitionLabel, ref probabilitySubsetImpliesSmallerLabel]
  where a = "A"


uniformeProbabilityMeasure :: Note
uniformeProbabilityMeasure = de $ do
  s ["The ", term "uniforme probability measure", " is a ", ix "probability measure", " that is only defined for measurable spaces with a finite ", universe]
  ma $ func prpm prsa (ccint 0 1 ⊆ reals) "A" (setsize "A" / setsize pruniv)


discreteProbabilityMeasure :: Note
discreteProbabilityMeasure = de $ do
  s ["The ", term "discrete probability measure", " is a ", ix "probability measure", " that is only defined for measure spaces with a countable ", universe]
  ma $ func prpm prsa (ccint 0 1 ⊆ reals) ("A" !: "i") ("p" !: "i")
