module Sets.Basics where

import           Notes

import           Functions.Application.Macro
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro

import           Sets.Basics.Macro
import           Sets.Basics.Terms

setBasics :: Note
setBasics = section "Set Basics" $ do
    setsSS
    subsetsSS
    universalSet
    emptySet
    singletonDefinition
    predicateSS

setsSS :: Note
setsSS = do
    setDefinition
    setElementNotation
    setEqualityDefinition
    setEqTransitivity

subsetsSS :: Note
subsetsSS = subsection "Subsets" $ do
    subsetDefinition
    subsetAntiSymmetry
    subsetTransitivity
    strictSubsetDefinition

universalSet :: Note
universalSet = subsection "The universal set" $ do
    universalSetDefinition
    universalSetSupsetOfAllSets

emptySet :: Note
emptySet = subsection "The empty set" $ do
    emptySetDefinition
    emptySetSubsetOfAllSets

predicateSS :: Note
predicateSS = subsection "Predicates" $ do
    predicateDefinition
    setComprehensionDefinition

singletonDefinition :: Note
singletonDefinition = do
    lab singletonDefinitionLabel
    de $ s ["A ", set, " with exactly one ", element, " is called a ", singleton']

setDefinition :: Note
setDefinition = de $ do
    lab setDefinitionLabel
    lab elementDefinitionLabel
    s ["A ", set', " is a ", ix "collection", " of distinct objects, considered as an object in its own right"]
    s ["These objects are called the ", element', "s of the ", set]

setElementNotation :: Note
setElementNotation = de $ do
    s ["The fact that a ", set, " ", m "A", " contains a certain ", element, " ", m "a", " is denoted as ", m $ "a" ∈ "A"]


setEqualityDefinition :: Note
setEqualityDefinition = de $ do
    lab setEqualityDefinitionLabel
    s ["Two ", sets, " ", m "A", " and ", m "B", " are ", defineTerm "equal", " if and only if they contain the same elements"]
    ma $ ("A" =§= "B") === (fa "x" $ ("x" ∈ "A") ∧ ("x" ∈ "B"))

setEqTransitivity :: Note
setEqTransitivity = thm $ do
    s ["The ", defineTerm "transitivity", " of ", quoted $ m seteqsign]
    newline

    s ["Let ", m "A", ", ", m "B", and , m "C", " be ", sets]

    ma $ do
        (pars ("A" =§= "B")
          ∧
         pars ("B" =§= "C"))
        ⇒
        ("A" =§= "C")

    proof $ do
        align_ $
            [
              (
                pars ("A" =§= "B")
                ∧
                pars ("B" =§= "C")
              )
              &
              (
                iffsign <>
                (pars $ fa "x" ("x" ∈ "A" ⇔ "x" ∈ "B"))
                  ∧
                (pars $ fa "x" ("x" ∈ "B" ⇔ "x" ∈ "C"))
              )
              ,
              "" &
              (
                impliessign <>
                fa "x"
                  (pars $ "x" ∈ "A" ⇔ "x" ∈ "B")
                  ∧
                  (pars $ "x" ∈ "B" ⇔ "x" ∈ "C")
              )
              ,
              "" &
              (
                iffsign <>
                fa "x" ("x" ∈ "A" ⇔ "x" ∈ "C")
              )
            ]


subsetDefinition :: Note
subsetDefinition = de $ do
    lab subsetDefinitionLabel
    s ["A ", set, " ", m "A", " is a ", subset', " of a ", set, " " , m "B", " if and only if ", m "B", " contains all elements of ", m "A"]
    ma $ ("A" ⊆ "B") === (fa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B")


subsetAntiSymmetry :: Note
subsetAntiSymmetry = thm $ do
    s ["The ", defineTerm "anti-symmetry", " of ", quoted $ m subseteqsign, ": ", newline, " Let ", m "A", " and ", m "B", " be ", sets]

    ma $ (pars $ "A" ⊆ "B" ∧ "B" ⊆ "A") ⇔ "A" =§= "B"

    proof $ do
        align_
            [
            ("A" ⊆ "B" ∧ "B" ⊆ "A")
            &
            iffsign <>
            (pars $ fa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B")
            ∧
            (pars $ fa "x" $ "x" ∈ "B" ⇒ "x" ∈ "A")
            ,
            "" &
            iffsign <>
            (
              fa "x" (
                (pars $ "x" ∈ "A" ⇒ "x" ∈ "B")
                ∧
                (pars $ "x" ∈ "B" ⇒ "x" ∈ "A")
              )
            )
            ,
            "" &
            iffsign <> (fa "x" ("x" ∈ "A" ⇔ "x" ∈ "B"))
            &
            "A" =§= "B"
            ]



subsetTransitivity :: Note
subsetTransitivity = thm $ do
    s ["The ", defineTerm "transitivity", " of ", quoted $ m subseteqsign, ": Let ", m "A", ", ", m "B", " and ", m "C", " be ", sets]
    ma $ do
        ("A" ⊆ "B") ∧ ("B" ⊆ "C") ⇒ ("A" ⊆ "C")

    proof $ do
        align_
            [
              ("A" ⊆ "B") ∧ ("B" ⊆ "C")
              &
              iffsign <>
              (pars $ fa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B") ∧ (pars $ fa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B")
              ,
              "" &
              impliessign <>
              (fa "x" ((pars $ "x" ∈ "A" ⇒ "x" ∈ "B") ∧ (pars $ "x" ∈ "B" ⇒ "x" ∈ "C")))
              ,
              "" &
              iffsign <>
              (fa "x" $ "x" ∈ "A" ⇒ "x" ∈ "C")
              &
              iffsign <>
              ("A" ⊆ "C")
            ]


strictSubsetDefinition :: Note
strictSubsetDefinition = de $ do
    s ["A ", set, " is a ", defineTerm "strict subset", " of another ", set, " if and only if ", m "A", " is a ", ix "subset", " of ", m "B", " and not equal to ", m "B"]
    ma $ ("A" `subsetneq` "B") === (("A" ⊆ "B") ∧ ("A" `setneq` "B"))


universalSetDefinition :: Note
universalSetDefinition = do
    de $ do
        s ["The ", defineTerm "universal set", " is the ", set, " of all objects"]
        ma $ setuniv === setcmpr "x" "true"
    nte $ do
        s ["Note that this is not well defined as this ", set, " would have to include itself.", " We will ignore this for now as the ", ix "universal set ", " is usually restricted to a domain that will be clear from the context"]

universalSetSupsetOfAllSets :: Note
universalSetSupsetOfAllSets = thm $ do
    lab everySetIsASubsetOfTheUniverseTheoremLabel
    s ["Every set ", m "A", " is a ", ix "subset", " of the ", ix "universal set", " ", m setuniv]
    ma $ fa "A" $ "A" ⊆ setuniv

    proof $ do
        s ["Let ", m "A", " be a set"]
        s ["Every element of ", m "A", " is contained in ", m setuniv]
        ma $ fa "x" $ (pars $ "x" ∈ "A") ⇒ (pars $ "x" ∈ setuniv)


emptySetDefinition :: Note
emptySetDefinition = de $ do
    s ["The ", defineTerm "empty set", " ", m emptyset, " is the ", set, " that contains no elements"]
    ma $ emptyset === setcmpr "x" "false"

emptySetSubsetOfAllSets :: Note
emptySetSubsetOfAllSets = thm $ do
    s ["The ", ix "empty set", " ", m emptyset, " is a ", ix "subset", " of all ", sets]
    proof $ do
        s ["Let ", m "A", " be a set."]
        s ["Every element of ", m emptyset, " is also an element of ", m "A"]

        ma $ fa "x" $ ("x" ∈ emptyset) ⇒ ("x" ∈ "A")

        "This is vacuously true."

predicateDefinition :: Note
predicateDefinition = de $ do
    lab predicateDefinitionLabel
    s ["A ", predicate', " ", m p, " over a ", set, " ", m aa, " is a ", subset, " of ", m aa]
    s ["Using a little notational overloading, ", m $ p `fn` a, " is said to hold if ", m a, " is an element of ", m aa]
    ma $ p `fn` a === a ∈ p
  where
    p = "P"
    a = "a"
    aa = "A"

setComprehensionDefinition :: Note
setComprehensionDefinition = de $ do
    s ["A formal description of a ", set, " using a ", predicate, " ", m "p", " is written as follows"]
    ma $ setcmpr ("x" ∈ "A") $ app "p" "x"
    s ["This is the ", set, " of all objects in ", m "A", " that satisfy the ", predicate, " ", m "P"]

