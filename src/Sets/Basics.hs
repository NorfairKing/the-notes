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

sets :: Note
sets = do
  setDefinition
  setElementNotation
  setComprehensionDefinition
  setEqualityDefinition
  setEqTransitivity

setDefinitionLabel :: Note
setDefinitionLabel = "de:set"

setDefinition :: Note
setDefinition = do
  label setDefinitionLabel
  de $ do
    "A "
    term "set"
    " is a "
    ix "collection"
    " of distinct objects, considered as an object in its own right."
    " These objects are called the "
    term "elements"
    " of the set."

setElementNotation :: Note
setElementNotation = do
  de $ do
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
setComprehensionDefinition = do
  de $ do
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
setEqualityDefinition = do
  label setEqualityDefinitionLabel
  de $ do
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
setEqTransitivity = do
  thm $ do
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

subsets :: Note
subsets = do
  subsetDefinition
  subsetAntiSymmetry

subsetDefinition :: Note
subsetDefinition = do
  de $ do
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
subsetAntiSymmetry = do
  thm $ do
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
