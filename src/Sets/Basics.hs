module Sets.Basics (
  basics

  , setEqualityDefinitionLabel
  , universalSetSupsetOfAllSetsLabel
  ) where

import           Notes

basics :: Notes
basics = notesPart "basics" body

body :: Note
body = do
  section "Set Basics"
  sets
  subsets
  universalSet
  emptySet
  singleton

sets :: Note
sets = do
  setDefinition
  setElementNotation
  setComprehensionDefinition
  setEqualityDefinition
  setEqTransitivity

subsets :: Note
subsets = do
  subsetDefinition
  subsetAntiSymmetry
  subsetTransitivity
  strictSubsetDefinition

universalSet :: Note
universalSet = do
  universalSetDefinition
  universalSetSupsetOfAllSets

emptySet :: Note
emptySet = do
  emptySetDefinition
  emptySetSubsetOfAllSets

singleton :: Note
singleton = de $ s ["A ", ix "set", " with exactly one element is called a ", term "singleton", "."]

setDefinitionLabel :: Label
setDefinitionLabel = delab "set"

setDefinition :: Note
setDefinition = de $ do
  lab setDefinitionLabel
  s ["A ", term "set", " is a ", ix "collection", " of distinct objects, considered as an object in its own right."]
  s ["These objects are called the ", term "elements", " of the set."]

setElementNotation :: Note
setElementNotation = de $ do
  s ["The fact that a ", ix "set", " ", m "A", " contains a certain ", ix "element", " ", m "a", " is denoted as ", m $ "a" ∈ "A", "."]

setComprehensionDefinition :: Note
setComprehensionDefinition = de $ do
  s ["A formal description of a ", ix "set", " using a ", ix "predicate", " ", m "p", " is written as follows:"]
  ma $ setcmpr "x" $ funapp "p" "x"
  s ["This is the ", ix "set", " of all objects that have the ", ix "property", " ", m "p", "."]

setEqualityDefinitionLabel :: Label
setEqualityDefinitionLabel = delab "sets-equality"

setEqualityDefinition :: Note
setEqualityDefinition = de $ do
  lab setEqualityDefinitionLabel
  s ["Two sets ", m "A", " and ", m "B", " are ", term "equal", " if and only if they contain the same elements."]
  ma $ ("A" =§= "B") === (fa "x" $ ("x" ∈ "A") &: ("x" ∈ "B"))

setEqTransitivity :: Note
setEqTransitivity = thm $ do
  s ["The ", term "transitivity", " of ", quoted $ m seteqsign, ": "]
  newline

  s ["Let ", m "A", ", ", m "B", " and ", m "C", " be sets."]

  ma $ do
    (pars ("A" =§= "B")
      &:
     pars ("B" =§= "C"))
    ⇒
    ("A" =§= "C")

  proof $ do
    align_ $
      [
        (
          pars ("A" =§= "B")
          &:
          pars ("B" =§= "C")
        )
        &
        (
          iffsign <>
          (pars $ fa "x" ("x" ∈ "A" ⇔ "x" ∈ "B"))
            &:
          (pars $ fa "x" ("x" ∈ "B" ⇔ "x" ∈ "C"))
        )
        ,
        "" &
        (
          impliessign <>
          fa "x"
            (pars $ "x" ∈ "A" ⇔ "x" ∈ "B")
            &:
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
  s ["A ", ix "set", " ", m "A", " is a ", term "subset", " of a set ", m "B", " if and only if ", m "B", " contains all elements of ", m "A", "."]
  ma $ ("A" ⊆ "B") === (fa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B")


subsetAntiSymmetry :: Note
subsetAntiSymmetry = thm $ do
  s ["The ", term "anti-symmetry", " of ", quoted $ m subseteqsign, ": ", newline, " Let ", m "A", " and ", m "B", " be sets."]

  ma $ (pars $ "A" ⊆ "B" &: "B" ⊆ "A") ⇔ "A" =§= "B"

  proof $ do
    align_
      [
      ("A" ⊆ "B" &: "B" ⊆ "A")
      &
      iffsign <>
      (pars $ fa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B")
      &:
      (pars $ fa "x" $ "x" ∈ "B" ⇒ "x" ∈ "A")
      ,
      "" &
      iffsign <>
      (
        fa "x" (
          (pars $ "x" ∈ "A" ⇒ "x" ∈ "B")
          &:
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
  s ["The ", term "transitivity", " of ", quoted $ m subseteqsign, ": Let ", m "A", ", ", m "B", " and ", m "C", " be sets."]
  ma $ do
    ("A" ⊆ "B") &: ("B" ⊆ "C") ⇒ ("A" ⊆ "C")

  proof $ do
    align_
      [
        ("A" ⊆ "B") &: ("B" ⊆ "C")
        &
        iffsign <>
        (pars $ fa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B") &: (pars $ fa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B")
        ,
        "" &
        impliessign <>
        (fa "x" ((pars $ "x" ∈ "A" ⇒ "x" ∈ "B") &: (pars $ "x" ∈ "B" ⇒ "x" ∈ "C")))
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
  s ["A ", ix "set", " is a ", term "strict subset", " of another ", ix "set", " if and only if ", m "A", " is a ", ix "subset", " of ", m "B", " and not equal to ", m "B"]
  ma $ ("A" `subsetneq` "B") === (("A" ⊆ "B") &: ("A" `setneq` "B"))


universalSetDefinition :: Note
universalSetDefinition = do
  de $ do
    s ["The ", term "universal set", " is the ", ix "set", " of all objects."]
    ma $ setuniv === setcmpr "x" "true"
  nte $ do
    s ["Note that this is well defined as this ", ix "set", " would have to include itself.", " We will ignore this for now as the ", ix "universal set ", " is usually restricted to a domain that will be clear from the context."]

universalSetSupsetOfAllSetsLabel :: Label
universalSetSupsetOfAllSetsLabel = thmlab "sets-every-set-is-a-subset-of-the-universe"

universalSetSupsetOfAllSets :: Note
universalSetSupsetOfAllSets = thm $ do
  lab universalSetSupsetOfAllSetsLabel
  s ["Every set ", m "A", " is a ", ix "subset", " of the ", ix "universal set", " ", m "setuniv", "."]
  ma $ fa "A" $ "A" ⊆ setuniv

  proof $ do
    s ["Let ", m "A", " be a set."]
    s ["Every element of ", m "A", " is contained in ", m setuniv, "."]
    ma $ fa "x" $ (pars $ "x" ∈ "A") ⇒ (pars $ "x" ∈ setuniv)


emptySetDefinition :: Note
emptySetDefinition = de $ do
  s ["The ", term "empty set", " ", m emptyset, " is the ", ix "set", " that contains no elements."]
  ma $ emptyset === setcmpr "x" "false"

emptySetSubsetOfAllSets :: Note
emptySetSubsetOfAllSets = thm $ do
  s ["The ", ix "empty set", " ", m emptyset, " is a ", ix "subset", " of all sets."]
  proof $ do
    s ["Let ", m "A", " be a set. "]
    s ["Every element of ", m emptyset, " is also an element of ", m "A", "."]

    ma $ fa "x" $ ("x" ∈ emptyset) ⇒ ("x" ∈ "A")

    "This is vacuously true."
