module Probability.SigmaAlgebra where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Probability.Intro.Terms
import           Sets.Algebra.Main              (secondLawOfDeMorganLabel, symmetricDifferenceITOUnionAndIntersectionLabel)
import           Sets.Basics

import           Probability.Intro.Macro

import           Probability.SigmaAlgebra.Macro
import           Probability.SigmaAlgebra.Terms

sigmaAlgebraS :: Note
sigmaAlgebraS = note "sigma-algebra" $ do
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



sigmaAlgebraDefinition :: Note
sigmaAlgebraDefinition = de $ do
    lab sigmaAlgebraDefinitionLabel
    s ["A ", sigmaAlgebra', " or ", term salgebra, " ", m sa_, " is a ", set, " of subsets of the ", universe_, " of a ", stochasticExperiment, " with the following three properties"]

    enumerate $ do
        item $ m $ univ_ ∈ sa_
        item $ m $ fa "A" $ ("A" ∈ sa_) ⇒ (setc "A" ∈ sa_)
        item $ m $ (fa (natural "n") (an ∈ sa_)) ⇒ ((setuncmp (natural "n") an) ∈ an)

  where
    an = "A" !: "n"

trivialSigmaAlgebraDefinition :: Note
trivialSigmaAlgebraDefinition = de $ do
    m $ setof $ emptyset <> ", " <> univ_
    " is called the "
    trivialSigmaAlgebra

measurableSpaceDefinition :: Note
measurableSpaceDefinition = de $ do
    s ["Let ", m univ_, " be the ", universe, " of a ", stochasticExperiment, " and let ", m sa_, " be a ", sa]
    s ["The ", ix "tuple", " ", m (univ_ <> ", " <> sa_), " is called a ", measurableSpace']


trivialMeasurableSpaceDefinition :: Note
trivialMeasurableSpaceDefinition = de $ do
    m $ univ_ <> ", " <> setof (emptyset <> ", " <> univ_)
    " is called the "
    term "trivial measurable space"
    "."

discreteSigmaAlgebraDefinitionLabel :: Label
discreteSigmaAlgebraDefinitionLabel = delab "discrete-sigma-algebra"

discreteSigmaAlgebraDefinition :: Note
discreteSigmaAlgebraDefinition = de $ do
    lab discreteSigmaAlgebraDefinitionLabel
    s ["The ", ix "powerset", " of a ", universe_ , " is called the ", term ("discrete " <> salgebra)]

saDec :: Note
saDec = s ["Let ", m sa_, " be a ", sa]


emptysetInSigmaAlgebra :: Note
emptysetInSigmaAlgebra = thm $ do
    saDec
    ma $ emptyset ∈ sa_

    proof $ do
        s ["The first two axioms", ref sigmaAlgebraDefinitionLabel, " together with ", m (setc univ_ =§= emptyset), " gives the theorem"]

sigmaAlgebraFiniteUnionLabel :: Label
sigmaAlgebraFiniteUnionLabel = thmlab "sigma-algebra-finite-union"

sigmaAlgebraFiniteUnion :: Note
sigmaAlgebraFiniteUnion = thm $ do
    lab sigmaAlgebraFiniteUnionLabel
    saDec
    ma $ pars (fa iInList $ ai ∈ sa_)
         ⇒
         (setuncmp iInList ai) ∈ sa_

    proof $ s ["Use the third axiom", ref sigmaAlgebraDefinitionLabel, " where only ", m "n", " sets ", m ai, " are non-empty"]

  where
    ai = "A" !: "i"
    iInList = "i" ∈ (setlst "1" "n")

sigmaAlgebraInfiniteIntersectionLabel :: Label
sigmaAlgebraInfiniteIntersectionLabel = thmlab "sigma-algebra-infinite-intersection"

sigmaAlgebraInfiniteIntersection :: Note
sigmaAlgebraInfiniteIntersection = thm $ do
    lab sigmaAlgebraInfiniteIntersectionLabel
    saDec
    ma $ pars (fa (natural "n") (an ∈ sa_))
         ⇒
         setuncmp (natural "n") an ∈ sa_

    proof $ s ["The first axiom", ref sigmaAlgebraDefinitionLabel, ", together with the finite union of events of a ", sa, ref sigmaAlgebraFiniteUnionLabel, " and the second law of De Morgan", ref secondLawOfDeMorganLabel, " give the proof"]

  where
    an = "A" !: "n"

sigmaAlgebraFiniteIntersectionLabel :: Label
sigmaAlgebraFiniteIntersectionLabel = thmlab "sigma-algebra-finite-intersection"

sigmaAlgebraFiniteIntersection :: Note
sigmaAlgebraFiniteIntersection = thm $ do
    lab sigmaAlgebraFiniteIntersectionLabel
    saDec

    ma $ pars (fa iInList $ ai ∈ sa_)
         ⇒
         (setincmp iInList ai) ∈ sa_

    proof $ s ["Use the infinite intersection of events in a ", sa , ref sigmaAlgebraInfiniteIntersectionLabel, " where only ", m "n", " sets ", m ai, " are not ", m univ_]

  where
    ai = "A" !: "i"
    iInList = "i" ∈ (setlst "1" "n")

sigmaAlgebraSetDifference :: Note
sigmaAlgebraSetDifference = thm $ do
    saDec

    ma $ fa ("A, B" ∈ sa_) (("A" `setsdiff` "B") ∈ sa_)

    proof $ do
        "The symmetric difference "
        m $ "A" `setsdiff` "B"
        " is equal to "
        m $ pars ("A" ∪ setc "B") ∩ pars (setc "A" ∪ "B")
        "."
        ref symmetricDifferenceITOUnionAndIntersectionLabel
        s ["Now use the finite union", ref sigmaAlgebraFiniteUnionLabel, " and the finite intersection", ref sigmaAlgebraFiniteIntersectionLabel, " of sets in a ", sa, " together with the second axiom", ref sigmaAlgebraDefinitionLabel]

unionIsNotSigmaAlgebraExample :: Note
unionIsNotSigmaAlgebraExample = cex $ do
    s ["The set union of two ", sa, "'s is not necessarily a ", sa]

    proof $ do
        s ["Take, for example, the ", sa, "'s ", m "B", " and ", m "A"]
        ma $ do
          "B = " <> setof (emptyset <> ", " <> setof "0" <> ", " <> setof "1,2" <> setof "0,1,2")
          comm1 "text" " and " -- TODO fix this
          "C = " <> setof (emptyset <> ", " <> setof "1" <> ", " <> setof "0,2" <> setof "0,1,2")

        s ["The union of ", m "B", " and ", m "C", " is ", emph "not", " a ", sa]
        ma $ "B" ∪ "C" =§= setof (emptyset <> ", " <> setof "0" <> ", " <> setof "1" <> ", " <> setof "0,2" <> ", " <> setof "1,2" <> ", " <> setof "0,1,2")

        s ["The union of ", m (setof "0"), " and ", m (setof "1"), ", for example, is not in ", m ("B" ∪ "C"), ".", ref sigmaAlgebraFiniteUnionLabel]


sagb :: Note
sagb = ix $ salgebra <> " generated by "

generatedSigmaAlgebraDefinition :: Note
generatedSigmaAlgebraDefinition = de $ do
    s ["Let ", m (gsa ⊆ univ_), " be a ", set, " of subsets of a ", universe]
    s ["The ", term (salgebra <> " generated by "), m gsa, " is the smallest ", sa, " that contains ", m gsa]
  where gsa = mathcal "C"

generatedSigmaAlgebraIsUnique :: Note
generatedSigmaAlgebraIsUnique = thm $ do
    s ["The ", sagb, " a ", set, " of subsets ", m gsa, " of a ", universe_, " is unique"]
    proof $ s ["This follows directly from the definition of equality of sets.", ref setEqualityDefinitionLabel]
  where gsa = mathcal "C"

generatedSigmaAlgebraExists :: Note
generatedSigmaAlgebraExists = thm $ do
    examq kul "Probability" "June 2014"
    s ["The ", sagb, " a ", set, " of subsets ", m gsa, " of a ", universe_, " always exists"]

    proof $ do
        s ["Let ", m saset, " be a set of sigma algebras as follows"]
        ma $ saset <> "=" <> setcmpr (ss ⊆ powset univ_) (ss <> text (" is a " <> sa <> " and ") <> gsa ⊆ ss)
        s [m saset, " is not empty because ", m (powset univ_), " is always a ", salgebra, ".", ref discreteSigmaAlgebraDefinitionLabel]
        s ["Let ", m sb, " be the following intersection"]
        ma $ sb <> "=" <> setincmp (ss ∈ saset) ss
        s [m sb, " definitely contains ", m gsa, " because ", m gsa, " is a subset of all ", m (ss ∈ saset)]

        s [" We will now show that ", m sb, " is a ", salgebra]
        enumerate $ do
            item $ do
                m $ univ_ ∈ sb
                newline
                s ["Every ", m ss, " in ", m (powset univ_), " contains ", m univ_, " because they are all ", salgebra, "s"]
                s [m sb, " must therefore contain ", m univ_]

            item $ do
                m $ fa ("B" ⊆ univ_) $ ("B" ∈ sb) ⇒ (setc "B" ∈ sb)
                newline
                s ["Let ", m "B", " be a subset of ", m univ_, " in ", m sb]
                s ["This means that ", m "B", " is also contained in every ", m ss, " of ", m saset]
                s ["Because every ", m ss, " in ", m saset, " is a ", salgebra, ", ", m ss, " must also contain ", m (setc "B"), ".",  ref sigmaAlgebraDefinitionLabel]
                s ["This means that ", m sb, " must also contains ", m (setc "B")]

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













