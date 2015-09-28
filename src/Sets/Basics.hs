module Sets.Basics (basics) where

import           Notes

basics :: Notes
basics = notesPart "basics" preamble body

preamble :: Note
preamble = return ()

body :: Note
body = do
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

setDefinitionLabel :: Note
setDefinitionLabel = "de:set"

setDefinition :: Note
setDefinition = de $ do
  label setDefinitionLabel
  "A "
  term "set"
  " is a "
  ix "collection"
  " of distinct objects, considered as an object in its own right."
  " These objects are called the "
  term "elements"
  " of the set."

setElementNotation :: Note
setElementNotation = de $ do
  "The fact that a "
  ix "set"
  " "
  m "A"
  " contains a certain "
  ix "element"
  " "
  m "a"
  " is denoted as "
  m $ in_ "a" "A"

setComprehensionDefinition :: Note
setComprehensionDefinition = de $ do
  "A formal description of a "
  ix "set"
  " using a "
  ix "predicate"
  " "
  m "p"
  " is written as follows:"
  ma $ do
    setcmpr "x" $ funapp "p" "x"
  "This is the "
  ix "set"
  " of all objects that have the "
  ix "property"
  " "
  m "p"
  "."

setEqualityDefinitionLabel :: Note
setEqualityDefinitionLabel = "de:sets-equality"

setEqualityDefinition :: Note
setEqualityDefinition = de $ do
  label setEqualityDefinitionLabel
  "Two sets "
  m "A"
  " and "
  m "B"
  " are "
  term "equal"
  " if and only if they contain the same elements."
  ma $ do
    "A" =§= "B"
    ===
    (mfa "x" $ do
      ("x" ∈ "A")
      &:
      ("x" ∈ "B"))


setEqTransitivity :: Note
setEqTransitivity = thm $ do
  "The "
  term "transitivity"
  " of "
  quoted $ m seteqsign
  ": "
  newline

  "Let "
  m "A"
  ", "
  m "B"
  " and "
  m "C"
  " be sets."

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
          (pars $ mfa "x" ("x" ∈ "A" ⇔ "x" ∈ "B"))
            &:
          (pars $ mfa "x" ("x" ∈ "B" ⇔ "x" ∈ "C"))
        )
        ,
        "" &
        (
          impliessign <>
          mfa "x"
            (pars $ "x" ∈ "A" ⇔ "x" ∈ "B")
            &:
            (pars $ "x" ∈ "B" ⇔ "x" ∈ "C")
        )
        ,
        "" &
        (
          iffsign <>
          mfa "x" ("x" ∈ "A" ⇔ "x" ∈ "C")
        )
      ]


subsetDefinition :: Note
subsetDefinition = de $ do
  "A "
  ix "set"
  " "
  m "A"
  " is a "
  term "subset"
  " of a set "
  m "B"
  " if and only if "
  m "B"
  " contains all elements of "
  m "A"

  ma $ do
    "A" ⊆ "B"
    ===
    (mfa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B")


subsetAntiSymmetry :: Note
subsetAntiSymmetry = thm $ do
  "The "
  term "anti-symmetry"
  " of "
  quoted $ m subseteqsign
  ": "
  newline
  " Let "
  m "A"
  " and "
  m "B"
  " be sets."

  ma $ (pars $ "A" ⊆ "B" &: "B" ⊆ "A") ⇔ "A" =§= "B"

  proof $ do
    align_
      [
      ("A" ⊆ "B" &: "B" ⊆ "A")
      &
      iffsign <>
      (pars $ mfa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B")
      &:
      (pars $ mfa "x" $ "x" ∈ "B" ⇒ "x" ∈ "A")
      ,
      "" &
      iffsign <>
      (
        mfa "x" (
          (pars $ "x" ∈ "A" ⇒ "x" ∈ "B")
          &:
          (pars $ "x" ∈ "B" ⇒ "x" ∈ "A")
        )
      )
      ,
      "" &
      iffsign <> (mfa "x" ("x" ∈ "A" ⇔ "x" ∈ "B"))
      &
      "A" =§= "B"
      ]



subsetTransitivity :: Note
subsetTransitivity = thm $ do
  sequence_ ["The ", term "transitivity", " of ", quoted $ m subseteqsign, ": Let ", m "A", ", ", m "B", " and ", m "C", " be sets."]
  ma $ do
    ("A" ⊆ "B") &: ("B" ⊆ "C") ⇒ ("A" ⊆ "C")

  proof $ do
    align_
      [
        ("A" ⊆ "B") &: ("B" ⊆ "C")
        &
        iffsign <>
        (pars $ mfa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B") &: (pars $ mfa "x" $ "x" ∈ "A" ⇒ "x" ∈ "B")
        ,
        "" &
        impliessign <>
        (mfa "x" ((pars $ "x" ∈ "A" ⇒ "x" ∈ "B") &: (pars $ "x" ∈ "B" ⇒ "x" ∈ "C")))
        ,
        "" &
        iffsign <>
        (mfa "x" $ "x" ∈ "A" ⇒ "x" ∈ "C")
        &
        iffsign <>
        ("A" ⊆ "C")
      ]


strictSubsetDefinition :: Note
strictSubsetDefinition = de $ do
  sequence_ ["A ", ix "set", " is a ", term "strict subset", " of another ", ix "set", " if and only if ", m "A", " is a ", ix "subset", " of ", m "B", " and not equal to ", m "B"]
  ma $ ("A" `subsetneq` "B") === (("A" ⊆ "B") &: ("A" `setneq` "B"))


universalSetDefinition :: Note
universalSetDefinition = do
  de $ do
    sequence_ ["The ", term "universal set", " is the ", ix "set", " of all objects."]
    ma $ setuniverse === setcmpr "x" "true"
  nte $ do
    "Note that this is well defined as this "
    ix "set"
    " would have to include itself."
    " We will ignore this for now as the "
    ix "universal set "
    " is usually restricted to a domain that will be clear from the context."

universalSetSupsetOfAllSetsLabel :: Note
universalSetSupsetOfAllSetsLabel = "thm:sets-every-set-is-a-subset-of-the-universe"

universalSetSupsetOfAllSets :: Note
universalSetSupsetOfAllSets = thm $ do
  label universalSetSupsetOfAllSetsLabel
  s ["Every set ", m "A", " is a ", ix "subset", " of the ", ix "universal set", " ", m "setuniverse", "."]
  ma $ mfa "A" $ "A" ⊆ setuniverse

  proof $ do
    s ["Let ", m "A", " be a set."]
    s ["Every element of ", m "A", " is contained in ", m setuniverse, "."]
    ma $ mfa "x" $ (pars $ "x" ∈ "A") ⇒ (pars $ "x" ∈ setuniverse)


emptySetDefinition :: Note
emptySetDefinition = de $ do
  sequence_ ["The ", term "empty set", " is the ", ix "set", " that contains no elements."]
  ma $ emptyset === setcmpr "x" "false"

emptySetSubsetOfAllSets :: Note
emptySetSubsetOfAllSets = thm $ do
  sequence_ ["The ", ix "empty set", m emptyset, " is a ", ix "subset", " of all sets."]
  proof $ do
    sequence_ ["Let ", m "A", " be a set. "]
    sequence_ ["Every element of ", m emptyset, " is also an element of ", m "A", "."]

    ma $ mfa "x" $ ("x" ∈ "emptyset") ⇒ ("x" ∈ "A")

    "This is vacuously true."
