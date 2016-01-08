module Computability.Symbols where

import           Notes

import           Functions.BinaryOperation.Terms
import           Sets.Basics.Terms

import           Computability.Symbols.Macro
import           Computability.Symbols.Terms

symbols :: Note
symbols = note "symbols-and-strings" $ do
    section "Symbols and strings"
    symbolDefinition
    alphabetDefinition
    stringDefinition
    emptyStringDefinition
    concatenationDefinition
    concatenationAssociative
    concatenationNotCommutative
    stringsOfAlphabetDefinition
    stringsWithEmptyDefinition
    reverseStringDefinition

symbolDefinition :: Note
symbolDefinition = de $ do
    lab symbolDefinitionLabel
    s ["A ", symbol', " is a representation of an abstract mathematical object."]
    s ["The only prerequisite of a ", symbol, " is that there is an equivalence relation ", m symEqSign, " defined on it"]
    refneeded "equivalence relation"

alphabetDefinition :: Note
alphabetDefinition = de $ do
    lab alphabetDefinitionLabel
    s ["An ", alphabet', " ", m alph_, " is a finite ", set, " of ", symbol, "s"]


stringDefinition :: Note
stringDefinition = de $ do
    lab stringDefinitionLabel
    s ["A ", string', " ", m str_, " over an ", alphabet, " ", m alph_, " is a ordered sequence of symbols ", m (a "i"), " in ", m alph_]
    ma $ str_ =: strlst (a 1) (a "n")
  where a n = "a" !: n

emptyStringDefinition :: Note
emptyStringDefinition = do
    lab emptyStringDefinitionLabel
    de $ s [the, emptyString', " ", m estr, " is the ", string, " of no symbols"]

    nte $ do
      s [m estr, " is just the notation for the empty string"]
      s ["It is only used because writing down ", quoted "nothing", ", even that word, is impractical"]

concatenationDefinition :: Note
concatenationDefinition = de $ do
    s [the, concatenation', " ",  m (x <@> y), " of two strings ", m x, and, m y, " is the following ", string]
    ma $ (x <@> y) === strof [x_ 1, x_ 2, dotsc, x_ "m", y_ 1, y_ 2, dotsc, y_ "n"]

  where
    x = "x"
    y = "y"
    x_ n = x !: n
    y_ n = y !: n

concatenationAssociative :: Note
concatenationAssociative = thm $ do
    s [the, concatenation, " of strings is ", associative_]

    toprove

concatenationNotCommutative :: Note
concatenationNotCommutative = thm $ do
    s [the, concatenation, " of strings is ", emph "not", " ", commutative]

    cexneeded

stringsOfAlphabetDefinition :: Note
stringsOfAlphabetDefinition = de $ do
    s ["The ", set, " of all strings over an ", alphabet, " ", m alph_, " is de:: Noted as ", m strsof_]
    ma $ strsof_ === setcmpr (strlist (a 1) (a 2) (a "n")) (cs [a "i" ∈ alph_, cs ["n", "i"] ∈ naturals])
  where a n = "a" !: n

stringsWithEmptyDefinition :: Note
stringsWithEmptyDefinition = do
    de $ s ["The ", set, " ", m $ alph_ ∪ setof estr, " is sometimes written more consisely as ", m alphe_]

    nte $ s ["This is not just a set of symbols because ", m estr, " is a string"]

reverseStringDefinition :: Note
reverseStringDefinition = de $ do
    lab reverseStringDefinitionLabel
    s [the, reverseString', " ", m (rstr str_), " of a ", string, " ", m (str_ =: strlst (a 1) (a n)), " is the ", string, " wherein the symbols of ", m str_, " are ordered in reverse"]
    ma $ rstr str_ === strlst (a n) (a 1)
  where
    a n = "a" !: n
    n = "n"
