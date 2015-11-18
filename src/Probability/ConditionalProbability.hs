module Probability.ConditionalProbability (
    conditionalProbability

  , conditionalProbabilityDefinitionLabel
  ) where

import           Notes

import           Sets.Partition (partition)

conditionalProbability :: Notes
conditionalProbability = notesPart "conditional-probability" body

body :: Note
body = do
  section "Conditional probibility"
  basics
  chainRule
  totalProbability
  bayesTheorem
  handyRules


basics :: Note
basics = do
  subsection "Basics"
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

psDec :: Note
psDec = s ["Let ", m prsp, " be a ", ix "probability space"]

conditionalProbabilityDefinition :: Note
conditionalProbabilityDefinition = de $ do
  lab conditionalProbabilityDefinitionLabel

  s [the, term "conditional probability", " of an ", event, m (a ∈ prsa), " given an ", event, m (b ∈ prsa), " with ", m (prob b /=: 0), " is denoted as ", m (cprob a b), ""]
  ma $ cprob a b === (prob (a ∩ b) /: prob b)

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


chainRule :: Note
chainRule = do
  subsection "Chain rule"
  thm $ do
    psDec
    s ["Let ", m (setlist (a 1) (a 2) (a k)), " be more than one event in ", m prsa]
    ma $
      prob (setincmpr (i =: 1) k (a i))
      =:
      prodcmpr (i =: 1) k (cprob (a i) (setincmpr (j =: 1) (i - 1) (a j)))
    ma $
      prob (a 1 ∩ a 2 ∩ dotsb ∩ a k)
      =:
      prob (a 1) * cprob (a 2) (a 1) * cprob (a 3) (a 1 ∩ a 2) * dotsb * cprob (a k) (a 1 ∩ a 2 ∩ dotsb ∩ a (k - 1))

    proof $ do
      s ["Proof by induction on ", m (naturals \\ setofs [1, 2])]
      itemize $ do
        item $ do
          s ["The theorem holds for ", m (k =: 2), ref conditionalProbabilityDefinitionLabel]
          ma $ cprob (a 1) (a 2) =: prob (a 1 ∩ a 2) /: prob (a 2) ⇒ prob (a 1 ∩ a 2) =: prob (a 1) * cprob (a 2) (a 1)

        item $ do
          s ["From the theorem for ", m (k =: n), " the theorem for ", m (k =: n + 1), " follows"]
          align_ $
            [
              prob (setincmpr (i =: 1) (n + 1) (a i))
            &      "" =: prob ((pars (setincmpr (i =: 1) n (a i))) ∩ (a (n + 1)))
            , "" & "" =:
                cprob (a (n + 1)) (pars $ setincmpr (i =: 1) n (a i))
              * prob (setincmpr (i =: 1) n (a i))
            , "" & "" =:
                cprob (a (n + 1)) (pars $ setincmpr (i =: 1) n (a i))
              * prodcmpr (i =: 1) n (cprob (a i) (setincmpr (j =: 1) (i - 1) (a j)))
            , "" & "" =:
                prodcmpr (i =: 1) (n + 1) (cprob (a i) (setincmpr (j =: 1) (i - 1) (a j)))
            ]
          s ["The base case is used in the second equation and the induction hypothesis is used in the second equation"]

  where
    a n = "A" !: n
    i = "i"
    j = "j"
    k = "k"
    n = "n"

psAndPartDec :: Note
psAndPartDec = do
  psDec
  s ["Let ", m x, " be a ", partition, " of ", m pruniv, " in which ", m (fa (a ∈ x) $ prob a > 0), " holds"]
  where x = "X"

totalProbabilityLabel :: Label
totalProbabilityLabel = Label Theorem "law-of-total-probability"

totalProbability :: Note
totalProbability = do
  subsection "Law of total probability"
  thm $ do
    lab totalProbabilityLabel
    examq "Probability" "August 2013"
    psAndPartDec
    ma $ fa (b ∈ prsa) $ prob b =: sumcmp (a ∈ x) (prob a * cprob b a)

    proof $ do
      align_
        [
          sumcmp (a ∈ x) (prob a * cprob b a)
        & "" =: sumcmp (a ∈ x) ((prob a * prob (a ∩ b)) /: prob a)
        , "" & "" =: sumcmp (a ∈ x) (prob (b ∩ a))
        , "" & "" =: prob (setuncmp (a ∈ x) (b ∩ a))
        , "" & "" =: prob (b ∩ setuncmp (a ∈ x) a)
        , "" & "" =: prob (b ∩ pruniv)  =: prob b
        ]
      s ["Note that the third equation only holds because ", m x, " is a partition of ", m pruniv, " and the sets ", m (b ∩ a), " are therefore disjunct "]
      s ["The fifth equation also only holds because ", m x, " is a partition of ", m pruniv]

  where
    x = "X"
    a = "A"
    b = "B"

bayesTheorem :: Note
bayesTheorem = do
  subsection "Bayes' theorem"
  thm $ do
    psAndPartDec
    s ["Let ", m b, " be an event in ", m prsa, " for which ", m (prob b > 0), " holds"]
    ma $ fa (a ∈ x) $ cprob a b =: (prob a * cprob b a) /: (sumcmp (c ∈ x) (prob c * cprob b c))

    proof $ do
      s ["Let ", m a, " be an event in ", m x]
      align_
        [
          (prob a * cprob b a) /: (sumcmp (c ∈ x) (prob c * cprob b c))
        & "" =: (prob a * cprob b a) /: (prob b)
        , "" & "" =: (prob a * (prob $ b ∩ a)) /: (prob b * prob a)
        , "" & "" =: prob (a ∩ b) /: prob b
        , "" & "" =: cprob a b
        ]
      s ["Note that the first equation holds by the law of total probability", ref totalProbabilityLabel]

  where
    x = "X"
    a = "A"
    b = "B"
    c = "C"

handyRules :: Note
handyRules = do
  subsection "Handy rules of computation"

  thm $ do
    psDec
    ma $ fa (cs [a, b] ∈ prsa) $ cprob a b =: (prob a /: prob b) * cprob b a

    proof $ do
      align_
        [
          cprob a b
        & "" =: prob (a ∩ b) /: prob b
        , "" & "" =: (prob a * prob (a ∩ b)) /: (prob b * prob a)
        , "" & "" =: (prob a /: prob b) * (prob (a ∩ b) /: prob a)
        , "" & "" =: (prob a /: prob b) * cprob b a
        ]

  thm $ do
    psAndPartDec
    ma $ fa (x ∈ pruniv) $ sumcmp (a ∈ x) (cprob a x) =: 1
    proof $ do
      s ["Let ", m x, " be an event in ", m pruniv]
      align_
        [
          sumcmp (a ∈ x) (cprob a x)
        & "" =: sumcmp (a ∈ x) ((prob $ a ∩ x) /: prob x)
        , "" & "" =: (sumcmp (a ∈ x) (prob $ a ∩ x)) /: prob x
        , "" & "" =: (prob $ setuncmp (a ∈ x) (a ∩ x)) /: prob x
        , "" & "" =: prob (pruniv ∩ x) /: prob x
        , "" & "" =: prob x /: prob x =: 1
        ]

  thm $ do
    psDec
    s ["Let ", m (setcmpr (a_ i) (i ∈ naturals)), " be a countable set in ", m prsa]
    ma $ prob (setuncmp (n ∈ naturals) (a_ n)) =: prob (a_ 1) + sumcmp (n > 1) (prob $ a_ n ∩ (setincmpr (i =: 1) (n - 1) (setc $ a_ i)))
    proof $ do
      s ["Proof by induction on ", m naturals]
      itemize $ do
        item $ do
          s ["The theorem holds for ", m (n =: 1)]
          ma $ prob (a_ 1 ∪ a_ 2)
            =: prob (a_ 1 ∪ pars (setc (a_ 1) ∩ a_ 2))
            =: prob (a_ 1) + prob (setc (a_ 1) ∩ a_ 2)
        item $ do
          s ["From the theorem for ", m (k =: n), " follows the theorem for ", m (k + 1)]
          ma $ prob (setuncmpr (i =: 1) (n + 1) (a_ i))
            =: prob (a_ (n + 1) ∪ setuncmpr (i =: 1) n (a_ i))
            =: prob (setc (pars $ setuncmpr (i =: 1) n (a_ i)) ∩ a_ (n + 1))
             + prob (setuncmpr (i =: 1) n (a_ i))
            =: prob (a_ 1)
             + sumcmp (n > 1) (prob (a_ n ∩ setuncmpr (i =: 1) (n - 1) (setc $ a_ i)))

  where
    x = "X"
    a = "A"
    a_ n = a !: n
    b = "B"
    i = "i"
    k = "k"
    n = "n"

