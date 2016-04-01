module Probability.ProbabilityMeasure where

import           Notes

import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Sets.Algebra.Complement.Terms
import           Sets.Basics.Terms

import           Probability.Intro.Macro
import           Probability.Intro.Terms
import           Probability.SigmaAlgebra.Macro
import           Probability.SigmaAlgebra.Terms

import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms

probabilityMeasureS :: Note
probabilityMeasureS = section "Probability Measures" $ do
    probabilityMeasureDefinition
    probabilityMeasureExample
    probabilitySpaceDefinition
    probabilityMeasureFiniteAdditivity
    probabilitySpaceProbabilityOfComplement
    probabilityPartitionByIntersection
    probabilityOfUnion
    unionBoundTheorem
    probabilityOfDifference
    probabilitySubsetImpliesSmaller
    probabilityAtMostOne

    traditionalProbabilityMeasures

traditionalProbabilityMeasures :: Note
traditionalProbabilityMeasures = subsection "Traditional Probability Measures" $ do
    uniformeProbabilityMeasureDefinition
    discreteProbabilityMeasureDefinition


msDec :: Note
msDec = s ["Let ", m mspace_, " be a ", measurableSpace]


probabilityMeasureDefinition :: Note
probabilityMeasureDefinition = de $ do
    lab probabilityMeasureDefinitionLabel
    lab countableAdditivityDefinitionLabel
    lab probabilityDefinitionLabel

    msDec
    s ["A ", probabilityMeasure', " is a ", function_, " ", m prm_, " with the following three properties:"]
    ma $ fun prm_ sa_ $ ccint 0 1

    enumerate $ do
        item $ m $ (prob univ_) =: 1
        item $ m $ fa ("A" ∈ sa_) ((prob "A") >=: 0)
        item $ do
            countableAdditivity'
            newline
            s ["Let ", m (sequ an "n"), " be a countably infinite ", sequence, " of pairwise disjunct sets"]
            ma $ prob (setuncmp (natural "n") an) =: sumcmp (natural "n") (prob an)

    s [m $ prob a, " is called the ", probability', " that ", m a, " happens"]
  where
    a = "A"
    an = "A" !: "n"

probabilityMeasureExample :: Note
probabilityMeasureExample = ex $ do
    let h = "Heads"
        t = "Tails"
        p = "p"
        u = setofs [h, t]
    s ["Let", m u, "be the universe of the", stochasticExperiment, "of throwing up a flipping an unfair coin"]
    s ["Let", m $ powset u, "be a", sigmaAlgebra]
    s [the, function, m prm_, "as follows is a", probabilityMeasure]
    ma $ fun prm_ (powset u) (ccint 0 1)
    ma $ cases $ do
        u & mapsto <> 1
        lnbk
        h & mapsto <> p
        lnbk
        t & mapsto <> (1 - p)
        lnbk
        emptyset & mapsto <> 0


msppsDec :: Note
msppsDec = s ["Let ", m mspace_, " be a ", measurableSpace, " and ", m prm_, " a ", probabilityMeasure]

probabilitySpaceDefinition :: Note
probabilitySpaceDefinition = de $ do
    lab probabilitySpaceDefinitionLabel
    s [msppsDec, m prsp_, " is called a ", probabilitySpace']

probabilityMeasureFiniteAdditivity :: Note
probabilityMeasureFiniteAdditivity = thm $ do
    lab probabilityMeasureFiniteAdditivityTheoremLabel

    s ["Let ", m prsp_, " be a ", probabilitySpace', " and let ", m (setcmpr an $ "n" ∈ setlst "1" "N"), " be ", m "N", " pairwise disjunct events of ", m sa_]
    ma $ prob (setuncmpr (n =: 1) "N" an) =: sumcmpr (n =: 1) "N" (prob an)

    proof $ s ["Use the ", countableAdditivity, " property of ", probabilityMeasure, "s", ref probabilityMeasureDefinitionLabel, " where only ", m n, " sets are non-empty"]
  where
    n = "n"
    an = "A" !: n

psDec :: Note
psDec = s ["Let ", m prsp_, " be a ", probabilitySpace]

probabilitySpaceProbabilityOfComplement :: Note
probabilitySpaceProbabilityOfComplement = thm $ do
    psDec
    ma $ fa (a ∈ sa_) (prob (setc a) =: (1 - prob a))

    proof $ do
        s ["Let ", m a, " be an event in ", m sa_]
        s ["The union of ", m a, " and its complement is ", m univ_, ".", ref unionComplementaryLawTheoremLabel]
        align_
            [
              univ_ & seteqsign <> (a ∪ setc a)
            , prob univ_ & "" =: prob (a ∪ setc a)
            , 1 & "" =: prob a + prob (setc a)
            , prob (setc a) & "" =: 1 - prob a
            ]

        s ["Notice that the second equivalence only holds because of the finite additivity propertiy of probability measures"]
        ref probabilityMeasureFiniteAdditivityTheoremLabel

    con $ m $ prob emptyset =: 0

  where a = "A"

probabilityPartitionByIntersection :: Note
probabilityPartitionByIntersection = prop $ do
    lab probabilityPartitionByIntersectionPropertyLabel

    psDec
    ma $ fa (a <> ", " <> b ∈ sa_) (prob b =: prob (b ∩ a) + prob (b ∩ setc a))

    proof $ do
      s ["Because ", m (b ∩ a), " and ", m (b ∩ setc a), " are disjunct, the theorem follows from the finite additivity property of probability measures"]
      ref probabilityMeasureFiniteAdditivityTheoremLabel

  where
    a = "A"
    b = "B"

probabilityOfUnion :: Note
probabilityOfUnion = prop $ do
    lab probabilityOfUnionPropertyLabel

    psDec
    ma $ fa (a <> ", " <> b ∈ sa_) (prob (a ∪ b) =: prob a + prob b - prob (a ∩ b))

    proof $ do
        s ["Let ", m a, " and ", m b, " be events in ", m sa_]
        align_
          [
            prob (a ∪ b) & "" =: prob (pars (a ∩ setc b) ∪ pars (a ∩ b) ∪ pars (setc a ∩ b))
          ,           "" & "" =: prob (a ∩ setc b) + prob (a ∩ b) + prob (setc a ∩ b)
          ,           "" & "" =: prob (a ∩ setc b) + prob (a ∩ b) + prob (setc a ∩ b) + pars (prob (a ∩ b) - prob (a ∩ b))
          ,           "" & "" =: pars (prob (a ∩ setc b) + prob (a ∩ b)) + pars (prob (setc a ∩ b) + prob (a ∩ b)) - prob (a ∩ b)
          ,           "" & "" =: prob a + prob b - prob (a ∩ b) ]
        "Note that we used the previous property in the last equation."
        ref probabilityPartitionByIntersectionPropertyLabel
  where
    a = "A"
    b = "B"

unionBoundTheorem :: Note
unionBoundTheorem = thm $ do
    lab unionBoundTheoremLabel
    psDec
    let a_ = "A"
        i = "i"
        a n = a_ !: n
    s ["Let", m $ cs [a 1, a 2, dotsc, a i, dotsc], "be a", countable, "set of events in", m sa_]
    ma $ prob (setuncmp i (a i)) <= sumcmp i (prob $ a i)

    toprove


probabilityOfDifference :: Note
probabilityOfDifference = prop $ do
    lab probabilityOfDifferencePropertyLabel

    psDec
    ma $ fa (a <> ", " <> b ∈ sa_) (prob (a `setdiff` b) =: prob (a ∪ b) - prob b)

    proof $ do
        s ["Let ", m a, " and ", m b, " be events in ", m sa_]
        ma $ prob (a ∪ b) =: prob (b `setdiff` pars (b ∩ setc a)) =: prob b + prob (a `setdiff` b)
        "Note that we used the equivalent definition of set difference in the first equation."
        ref setDifferenceEquivalentDefinitionTheoremLabel
  where
    a = "A"
    b = "B"

probabilitySubsetImpliesSmaller :: Note
probabilitySubsetImpliesSmaller = prop $ do
     lab probabilitySubsetImpliesSmallerProbabilityPropertyLabel

     psDec
     ma $ fa (a <> ", " <> b ∈ sa_) ((a ⊆ b) ⇒ (prob a <= prob b))

     proof $ do
         ma $ prob a =: prob (b `setdiff` pars (b ∩ a)) =: prob b - prob (b ∩ a) <= prob b

         s ["Note that in the first equation we used that ", m a, " is a subset of ", m b, " and in the second equation, we used the previous property"]
         ref probabilityOfDifferencePropertyLabel
  where
    a = "A"
    b = "B"


probabilityAtMostOne :: Note
probabilityAtMostOne = prop $ do
    psDec

    ma $ fa (a ∈ sa_) (prob a <= 1)
    proof $ do
        s ["Every set ", m a, " is a subset of ", m univ_, ref everySetIsASubsetOfTheUniverseTheoremLabel]
        s [" so ", m (prob a), " must be smaller than ", m (prob univ_ =: 1), ref probabilityMeasureDefinitionLabel, ref probabilitySubsetImpliesSmallerProbabilityPropertyLabel]
  where a = "A"


uniformeProbabilityMeasureDefinition :: Note
uniformeProbabilityMeasureDefinition = de $ do
    lab uniformeProbabilityMeasureDefinitionLabel
    s ["The ", uniformeProbabilityMeasure', " is a ", probabilityMeasure, " that is only defined for measurable spaces with a finite ", universe]
    ma $ func prm_ sa_ (ccint 0 1 ⊆ reals) "A" (setsize "A" / setsize univ_)


discreteProbabilityMeasureDefinition :: Note
discreteProbabilityMeasureDefinition = de $ do
    lab discreteProbabilityMeasureDefinitionLabel
    s ["The ", discreteProbabilityMeasure', " is a ", probabilityMeasure, " that is only defined for measure spaces with a countable ", universe]
    ma $ func prm_ sa_ (ccint 0 1 ⊆ reals) ("A" !: "i") ("p" !: "i")


