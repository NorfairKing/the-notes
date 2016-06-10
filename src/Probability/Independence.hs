module Probability.Independence where

import           Notes

import qualified Prelude                                  as P

import           Functions.Basics.Macro
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Sets.Basics.Terms

import           Probability.ConditionalProbability.Macro
import           Probability.Intro.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.SigmaAlgebra.Macro
import           Probability.SigmaAlgebra.Terms

import           Probability.Independence.Macro
import           Probability.Independence.Terms


independenceS :: Note
independenceS = section "Independence" $ do
    independenceDefinition
    independenceExamples
    dependenceDefinition
    conditionalProbabilityIndependentEvents
    pairwiseIndependenceDefinition
    mutualIndependenceDefinition
    mutualIndependenceImpliesPairwiseIndependence
    infiniteMutalIndependenceDefinition

    conditionalIndependenceSS

psDec :: Note
psDec = s ["Let ", m prsp_, " be a ", probabilitySpace]

independenceDefinition :: Note
independenceDefinition = de $ do
    lab independentDefinitionLabel
    psDec
    s ["Two events ", m a, and, m b, " in ", m sa_, " are called ", independent', " if the following equality holds"]
    ma $ ind a b === (prob (a ∩ b) =: prob a * prob b)

  where
    a = "A"
    b = "B"

independenceExamples :: Note
independenceExamples = ex $ do
    longhandIndependenceExample
    coinTossExample

longhandIndependenceExample :: Note
longhandIndependenceExample = ex $ do
    let h = "H"
        t = "T"
        hh = h <> h
        ht = h <> t
        th = t <> h
        tt = t <> t
        u = setofs [hh, ht, th, tt]
    s ["Let", m u, "be the", universe, "of the", stochasticExperiment, dquoted "Flipping two coins"]
    s ["Using the", discreteSigmaAlgebra, "on this", universe, "we define the following", probabilityMeasure]
    ma $ fun prm_ (powset u) (ccint 0 1)
    ma $ cases $ mapstofun
        [
          (emptyset             , 0)
        , (setofs [hh]          , 1 /: 4)
        , (setofs [ht]          , 1 /: 4)
        , (setofs [th]          , 1 /: 4)
        , (setofs [tt]          , 1 /: 4)
        , (setofs [hh, ht]      , 1 /: 2)
        , (setofs [hh, th]      , 1 /: 2)
        , (setofs [hh, tt]      , 1 /: 2)
        , (setofs [ht, th]      , 1 /: 2)
        , (setofs [ht, tt]      , 1 /: 2)
        , (setofs [th, tt]      , 1 /: 2)
        , (setofs [hh, ht, th]  , 3 /: 4)
        , (setofs [hh, ht, tt]  , 3 /: 4)
        , (setofs [hh, th, tt]  , 3 /: 4)
        , (setofs [ht, th, tt]  , 3 /: 4)
        , (u                    , 1)
        ]
    s ["This", probabilityMeasure, "corresponds with our intuition of the situation"]
    newline

    s ["The events", m $ setof hh, and, m $ setof ht, "are not", independent]
    ma $ prob (setof hh ∩ setof ht) =: 0 <> quad <> text "while" <> quad <> prob hh * prob ht =: 1 /: 4
    s ["The events", m $ setofs [ht, th], and, m $ setofs [ht, tt], "are", independent]
    ma $ prob (setofs [ht, th] ∩ setofs [ht, tt]) =: prob (setof ht) =: 1 /: 4 <> quad <> text "and" <> quad <>  prob (setofs [ht, th]) * prob (setofs [ht, tt]) =: (1 /: 2) `cdot` (1 /: 2)
  where
    mapstofun :: [(Note, Note)] -> Note
    mapstofun = P.sequence_ . P.map (<> lnbk) . P.map (\(a, b) -> a & mapsto <> b)

coinTossExample :: Note
coinTossExample = ex $ do
    let h = "H"
        t = "T"
        p = "p"
        n = "n"
    s ["A coin is tossed independently and repeatedly with a", probability, "of", m p, "of", m h]
    s [the, probability, "of only", m h, "in the first", m n, "tosses is", m (p ^ n)]
    ma $ prob (h !: 1 ∧ h !: 2 ∧ dotsb ∧ h !: n) =: prob (h !: 1) * prob (h !: 2) * dotsb * prob (h !: n) =: p ^ n
    s [the, probability, "of obtaining the first", m t, "on the", m n, "-th toss"]
    ma $ prob (h !: 1 ∧ h !: 2 ∧ dotsb ∧ h !: (n - 1) ∧ t !: n) =: prob (h !: 1) * prob (h !: 2) * dotsb * prob (h !: (n - 1)) * prob (t !: n) =: p ^ (n - 1) * (pars $ 1 - p)



dependenceDefinition :: Note
dependenceDefinition = de $ do
    psDec
    s ["If two events ", m a, and, m b, " in ", m sa_, " are not ", independent, ", they are called ", dependent', " events"]
    s ["This depedence is called.."]
    itemize $ do
        item $ s [positiveDependence', " if ", m (prob (a ∩ b) > prob a * prob b), " holds"]
        item $ s [negativeDependence', " if ", m (prob (a ∩ b) < prob a * prob b), " holds"]

  where
    a = "A"
    b = "B"

conditionalProbabilityIndependentEvents :: Note
conditionalProbabilityIndependentEvents = thm $ do
    psDec
    s ["Let ", m a, and, m b, " be two ", independent, " events in ", m sa_]
    ma $ cprob a b =: prob a

    proof $ do
        ma $ cprob a b =: prob (a ∩ b) /: prob b =: (prob a * prob b) /: prob b =: prob a

  where
    a = "A"
    b = "B"

pairwiseIndependenceDefinition :: Note
pairwiseIndependenceDefinition = de $ do
    s ["A set of events is called ", pairwiseIndependent', " if every two events in the set are ", independent]

mutualIndependenceDefinition :: Note
mutualIndependenceDefinition = de $ do
    psDec
    s ["A set ", m x, " of events is called ", mutuallyIndependent', " if the following holds"]
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
    s ["An infinite ", set, " of events is called ", mutuallyIndependent, " if every finite subset is mutually independent"]



conditionalIndependenceSS :: Note
conditionalIndependenceSS = subsection "Conditional Independence" $ do
    conditionalIndenpendenceDefinition


    conditionalIndependenceSymmetry
    conditionalIndependenceDecomposition
    conditionalIndependenceContraction
    conditionalIndependenceWeakUnion
    conditionalIndependenceIntersection

conditionalIndenpendenceDefinition :: Note
conditionalIndenpendenceDefinition = do
    let (a, b, c) = ("A", "B", "C")
    de $ do
        lab conditionallyIndependentDefinitionLabel
        s ["Two", events, m a, and, m b, "are", conditionallyIndependent, "given a third", event, m c, "precisely if the occurrence or non-occurrence of", m a, "and the occurrence or non-occurrence of", m b, "are", independent, events, ", given", m c]
        ma $ cind a b c === (cprob (a ∩ b) c =: cprob a c * cprob b c)

    nte $ do
        s ["There is an intuitive way to go about imagining this concept"]
        s [m a, and, m b, "are not", independent, "but if it is given that", m c, "has happened, then", m a, and, m b, "will seem independent"]



conditionalIndependenceSymmetry :: Note
conditionalIndependenceSymmetry = thm $ do
    psDec
    let (a, b, c) = ("A", "B", "C")
    s ["Let", m a, ", ", m b, and, m c, "be events in", m sa_]
    ma $ cind a b c ⇔ cind b a c
    toprove

conditionalIndependenceDecomposition :: Note
conditionalIndependenceDecomposition = thm $ do
    psDec
    let (a, b, c, d) = ("A", "B", "C", "D")
    s ["Let", m a, ", ", m b, and, m c, "be events in", m sa_]
    ma $ cind a (b ∩ d) c ⇒ cind a b c
    toprove

conditionalIndependenceContraction :: Note
conditionalIndependenceContraction = thm $ do
    psDec
    let (a, b, c, d) = ("A", "B", "C", "D")
    s ["Let", m a, ", ", m b, and, m c, "be events in", m sa_]
    ma $ cind a b c ∧ cind a d (b ∩ c) ⇒ cind a b (c ∩ d)
    toprove

conditionalIndependenceWeakUnion :: Note
conditionalIndependenceWeakUnion = thm $ do
    psDec
    let (a, b, c, d) = ("A", "B", "C", "D")
    s ["Let", m a, ", ", m b, and, m c, "be events in", m sa_]
    ma $ cind a (b ∩ d) c ⇒ cind a b (c ∩ d)
    toprove

conditionalIndependenceIntersection :: Note
conditionalIndependenceIntersection = thm $ do
    psDec
    let (a, b, c, d) = ("A", "B", "C", "D")
    s ["Let", m a, ", ", m b, and, m c, "be events in", m sa_, "with a strictly positive probability"]
    ma $ cind a b (c ∩ d) ∧ cind a d (b ∩ c) ⇒ cind a b (c ∩ d)
    toprove

