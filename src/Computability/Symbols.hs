module Computability.Symbols (
    symbols

  , symbol
  , alphabet
  , concatenation
  ) where

import           Notes

symbols :: Notes
symbols = notesPart "symbols-and-strings" body

body :: Note
body = do
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

symbol :: Note
symbol = ix "symbol"

symbolDefinition :: Note
symbolDefinition = de $ do
  s ["A ", term "symbol", " is a representation of an abstract mathematical object."]
  s ["The only prerequisite of a symbol is that there is an equivalence relation ", m csymEqSign, " defined on it"]
  refneeded "equivalence relation"

alphabet :: Note
alphabet = ix "alphabet"

alphabetDefinition :: Note
alphabetDefinition = de $ do
  s ["An ", term "alphabet", " ", m calph, " is a finite set of ", symbol, "s"]

stringDefinition :: Note
stringDefinition = de $ do
  s ["A ", term "string", " ", m cstr, " over an alphabet ", m calph, " is a ordered sequence of symbols ", m (a "i"), " in ", m calph]
  ma $ cstr =: cstrlst (a 1) (a "n")
  where a n = "a" !: n

emptyStringDefinition :: Note
emptyStringDefinition = do
  de $ s [the, term "empty string", " ", m cestr, " is the string of no symbols"]

  nte $ do
    s [m cestr, " is just the notation for the empty string"]
    s ["It is only used because writing down ", quoted "nothing", ", even that word, is impractical"]

concatenation :: Note
concatenation = ix "concatenation"

concatenationDefinition :: Note
concatenationDefinition = de $ do
  s [the, term "concatenation", " ",  m (x <@> y), " of two strings ", m x, and, m y, " is the following string"]
  ma $ (x <@> y) === cstrof [x_ 1, x_ 2, dotsc, x_ "m", y_ 1, y_ 2, dotsc, y_ "n"]

  where
    x = "x"
    y = "y"
    x_ n = x !: n
    y_ n = y !: n

concatenationAssociative :: Note
concatenationAssociative = thm $ do
  s [the, concatenation, " of strings is ", associative]

  toprove

concatenationNotCommutative :: Note
concatenationNotCommutative = thm $ do
  s [the, concatenation, " of strings is ", emph "not", " ", commutative]

  cexneeded

stringsOfAlphabetDefinition :: Note
stringsOfAlphabetDefinition = de $ do
  s ["The set of all strings over an alphabet ", m calph, " is denoted as ", m cstrs]
  ma $ cstrs === setcmpr (cstrlist (a 1) (a 2) (a "n")) (cs [a "i" ∈ cstrs, cs ["n", "i"] ∈ naturals])
  where a n = "a" !: n

stringsWithEmptyDefinition :: Note
stringsWithEmptyDefinition = do
  de $ s ["The set ", m (calph ∪ (setof cestr)), " is sometimes written more consisely as ", m calphe]

  nte $ s ["This is not just a set of symbols because ", m cestr, " is a string"]

reverseStringDefinition :: Note
reverseStringDefinition = de $ do
  s [the, term "reverse string", " ", m (crstr cstr), " of a string ", m (cstr =: cstrlst (a 1) (a n)), " is the string wherein the symbols of ", m cstr, " are ordered in reverse"]
  ma $ crstr cstr === cstrlst (a n) (a 1)
  where
    a n = "a" !: n
    n = "n"
