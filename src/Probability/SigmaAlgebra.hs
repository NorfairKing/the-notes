module Probability.SigmaAlgebra (
  sigmaAlgebra

  , discreteSigmaAlgebraDefinitionLabel
  ) where

import           Notes
import           Sets.Algebra (secondLawOfDeMorganLabel,
                               symmetricDifferenceITOUnionAndIntersectionLabel)
import           Sets.Basics  (setEqualityDefinitionLabel)

sigmaAlgebra :: Notes
sigmaAlgebra = notesPart "sigma-algebra" body

body :: Note
body = do
  section "Sigma Algebra's"
  sigmaAlgebraBasics
  generatedSigmaAlgebra

sigmaAlgebraBasics :: Note
sigmaAlgebraBasics = do
  sigmaAlgebraDefinition
  trivialSigmaAlgebraDefinition
  measurableSpaceDefinition
  trivialMeasurableSpaceDefinition
  discreteSigmaAlgebraDefinition
  emptysetInSigmaAlgebra
  sigmaAlgebraFiniteUnion
  sigmaAlgebraInfiniteIntersection
  sigmaAlgebraFiniteIntersection
  sigmaAlgebraSetDifference
  unionIsNotSigmaAlgebraExample

generatedSigmaAlgebra :: Note
generatedSigmaAlgebra = do
  subsection $ "Generating " <> sa <> "s"
  generatedSigmaAlgebraDefinition
  generatedSigmaAlgebraIsUnique
  generatedSigmaAlgebraExists



sigmaAlgebraDefinitionLabel :: Note
sigmaAlgebraDefinitionLabel = "de:sigma-algebra"

sigmaAlgebraDefinition :: Note
sigmaAlgebraDefinition = de $ do
  label sigmaAlgebraDefinitionLabel
  s ["A ", term "Sigma Algebra", " or ", term salgebra, " ", m prsa, " is a ", set, " of subsets of the ", universe_, " of a ", ix "stochastic experiment", " with the following three properties."]

  enumerate $ do
    item $ m $ pruniv ∈ prsa
    item $ m $ fa "A" $ ("A" ∈ prsa) ⇒ (setc "A" ∈ prsa)
    item $ m $ (fa (natural "n") (an ∈ prsa)) ⇒ ((setuncmp (natural "n") an) ∈ an)

  where
    an = "A" !: "n"

trivialSigmaAlgebraDefinition :: Note
trivialSigmaAlgebraDefinition = de $ do
  m $ setof $ emptyset <> ", " <> pruniv
  " is called the "
  term $ "trivial " <> salgebra

measurableSpaceDefinition :: Note
measurableSpaceDefinition = de $ do
  s ["Let ", m pruniv, " be the ", universe, " of a ", ix "stochastic experiment", " and let ", m prsa, " be a ", sa, "."]
  s ["The ", ix "tuple", " ", m (pruniv <> ", " <> prsa), " is called a ", term "measurable space"]


trivialMeasurableSpaceDefinition :: Note
trivialMeasurableSpaceDefinition = de $ do
  m $ pruniv <> ", " <> setof (emptyset <> ", " <> pruniv)
  " is called the "
  term "trivial measurable space"
  "."

discreteSigmaAlgebraDefinitionLabel :: Note
discreteSigmaAlgebraDefinitionLabel = "de:discrete-sigma-algebra"

discreteSigmaAlgebraDefinition :: Note
discreteSigmaAlgebraDefinition = de $ do
  label discreteSigmaAlgebraDefinitionLabel
  s ["The ", ix "powerset", " of a ", universe_ , " is called the ", term ("discrete " <> salgebra), "."]

saDec :: Note
saDec = s ["Let ", m prsa, " be a ", sa, "."]


emptysetInSigmaAlgebra :: Note
emptysetInSigmaAlgebra = thm $ do
  saDec
  ma $ emptyset ∈ prsa

  proof $ do
    s ["The first two axioms", deref sigmaAlgebraDefinitionLabel, " together with ", m (setc pruniv =§= emptyset), " gives the theorem."]

sigmaAlgebraFiniteUnionLabel :: Note
sigmaAlgebraFiniteUnionLabel = "th:sigma-algebra-finite-union"

sigmaAlgebraFiniteUnion :: Note
sigmaAlgebraFiniteUnion = thm $ do
  label sigmaAlgebraFiniteUnionLabel
  saDec
  ma $ pars (fa iInList $ ai ∈ prsa)
       ⇒
       (setuncmp iInList ai) ∈ prsa

  proof $ s ["Use the third axiom", deref sigmaAlgebraDefinitionLabel, " where only ", m "n", " sets ", m ai, " are non-empty."]

  where
    ai = "A" !: "i"
    iInList = "i" ∈ (setlst "1" "n")

sigmaAlgebraInfiniteIntersectionLabel :: Note
sigmaAlgebraInfiniteIntersectionLabel = "th:sigma-algebra-infinite-intersection"

sigmaAlgebraInfiniteIntersection :: Note
sigmaAlgebraInfiniteIntersection = thm $ do
  label sigmaAlgebraInfiniteIntersectionLabel
  saDec
  ma $ pars (fa (natural "n") (an ∈ prsa))
       ⇒
       setuncmp (natural "n") an ∈ prsa

  proof $ s ["The first axiom", deref sigmaAlgebraDefinitionLabel, ", together with the finite union of events of a ", sa, thmref sigmaAlgebraFiniteUnionLabel, " and the second law of De Morgan", thmref secondLawOfDeMorganLabel, " give the proof."]

  where
    an = "A" !: "n"

sigmaAlgebraFiniteIntersectionLabel :: Note
sigmaAlgebraFiniteIntersectionLabel = "thm:sigma-algebra-infinite-intersection"

sigmaAlgebraFiniteIntersection :: Note
sigmaAlgebraFiniteIntersection = thm $ do
  label sigmaAlgebraFiniteIntersectionLabel
  saDec

  ma $ pars (fa iInList $ ai ∈ prsa)
       ⇒
       (setincmp iInList ai) ∈ prsa

  proof $ s ["Use the infinite intersection of events in a ", sa , thmref sigmaAlgebraInfiniteIntersectionLabel, " where only ", m "n", " sets ", m ai, " are not ", m pruniv, "."]

  where
    ai = "A" !: "i"
    iInList = "i" ∈ (setlst "1" "n")

sigmaAlgebraSetDifference :: Note
sigmaAlgebraSetDifference = thm $ do
  saDec

  ma $ fa ("A, B" ∈ prsa) (("A" `setsdiff` "B") ∈ prsa)

  proof $ do
    "The symmetric difference "
    m $ "A" `setsdiff` "B"
    " is equal to "
    m $ pars ("A" ∪ setc "B") ∩ pars (setc "A" ∪ "B")
    "."
    thmref symmetricDifferenceITOUnionAndIntersectionLabel
    s ["Now use the finite union", thmref sigmaAlgebraFiniteUnionLabel, " and the finite intersection", thmref sigmaAlgebraFiniteIntersectionLabel, " of sets in a ", sa, " together with the second axiom", deref sigmaAlgebraDefinitionLabel, "."]

unionIsNotSigmaAlgebraExample :: Note
unionIsNotSigmaAlgebraExample = cex $ do
  s ["The set union of two ", sa, "'s is not necessarily a ", sa, "."]

  proof $ do
    s ["Take, for example, the ", sa, "'s ", m "B", " and ", m "C", ":"]
    ma $ do
      "B = " <> setof (emptyset <> ", " <> setof "0" <> ", " <> setof "1,2" <> setof "0,1,2")
      comm1 "text" " and " -- TODO fix this
      "C = " <> setof (emptyset <> ", " <> setof "1" <> ", " <> setof "0,2" <> setof "0,1,2")

    s ["The union of ", m "B", " and ", m "C", " is ", emph "not", " a ", sa]
    ma $ "B" ∪ "C" =§= setof (emptyset <> ", " <> setof "0" <> ", " <> setof "1" <> ", " <> setof "0,2" <> ", " <> setof "1,2" <> ", " <> setof "0,1,2")

    s ["The union of ", m (setof "0"), " and ", m (setof "1"), ", for example, is not in ", m ("B" ∪ "C"), ".", thmref sigmaAlgebraFiniteUnionLabel]


sagb :: Note
sagb = ix $ salgebra <> " generated by "

generatedSigmaAlgebraDefinition :: Note
generatedSigmaAlgebraDefinition = de $ do
  s ["Let ", m (gsa ⊆ pruniv), " be a ", set, " of subsets of a ", universe, "."]
  s ["The ", term (salgebra <> " generated by "), m gsa, " is the smallest ", sa, " that contains ", m gsa, "."]
  where gsa = mathcal "C"

generatedSigmaAlgebraIsUnique :: Note
generatedSigmaAlgebraIsUnique = thm $ do
  s ["The ", sagb, " a ", set, " of subsets ", m gsa, " of a ", universe_, " is unique."]
  proof $ s ["This follows directly from the definition of equality of sets.", deref setEqualityDefinitionLabel]
  where gsa = mathcal "C"

generatedSigmaAlgebraExists :: Note
generatedSigmaAlgebraExists = thm $ do
  examq "Probability" "June 2014"
  s ["The ", sagb, " a ", set, " of subsets ", m gsa, " of a ", universe_, " always exists."]

  proof $ do
    s ["Let ", m saset, " be a set of sigma algebras as follows:"]
    ma $ saset <> "=" <> setcmpr (ss ⊆ powset pruniv) (ss <> text (" is a " <> sa <> " and ") <> gsa ⊆ ss)
    s [m saset, " is not empty because ", m (powset pruniv), " is always a ", salgebra, ".", deref discreteSigmaAlgebraDefinitionLabel]
    s ["Let ", m sb, " be the following intersection:"]
    ma $ sb <> "=" <> setincmp (ss ∈ saset) ss
    s [m sb, " definitely contains ", m gsa, " because ", m gsa, " is a subset of all ", m (ss ∈ saset), "."]

    s [" We will now show that ", m sb, " is a ", salgebra, "."]
    enumerate $ do
      item $ do
        m $ pruniv ∈ sb
        newline
        s ["Every ", m ss, " in ", m (powset pruniv), " contains ", m pruniv, " because they are all ", salgebra, "s."]
        s [m sb, " must therefore contain ", m pruniv, "."]

      item $ do
        m $ fa ("B" ⊆ pruniv) $ ("B" ∈ sb) ⇒ (setc "B" ∈ sb)
        newline
        s ["Let ", m "B", " be a subset of ", m pruniv, " in ", m sb, "."]
        s ["This means that ", m "B", " is also contained in every ", m ss, " of ", m saset, "."]
        s ["Because every ", m ss, " in ", m saset, " is a ", salgebra, ", ", m ss, " must also contain ", m (setc "B"), ".",  deref sigmaAlgebraDefinitionLabel]
        s ["This means that ", m sb, " must also contains ", m (setc "B"), "."]

      item $ do
        m $ (pars $ fa (natural "n") (bn ∈ sb)) ⇒ ((setuncmp (natural "n") bn) ∈ sb)
        newline
        "The reasoning for this part is analogous to the reasoning for the previous part."

  where
    saset = "X"
    ss = mathcal "A"
    sb = mathcal "B"
    gsa = mathcal "C"
    bn = "B" !: "n"













