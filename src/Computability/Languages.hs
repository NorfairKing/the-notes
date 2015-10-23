module Computability.Languages (
    languages

  , language
  ) where

import           Notes

import           Computability.Symbols (concatenation)

languages :: Notes
languages = notesPart "languages" body

body :: Note
body = do
  section "Languages"

  languageDefinition
  languageConcatenationDefinition
  concatenationAssociative
  concatenationNotCommutative
  selfConcatenationDefinition
  kleeneStarDefinition
  languagePlusDefinition
  languesOverAlphabetDefinition
  infiniteLanguagesCountable
  uncountablyManyLanguages
  reverseLanguage

language :: Note
language = ix "language"

languageDefinition :: Note
languageDefinition = de $ do
  s ["A ", term "language", " over an alphabet ", m (calph), " is a set of finite strings over that alphabet"]

languageConcatenationDefinition :: Note
languageConcatenationDefinition = de $ do
  s ["The ", term "concatenation", " ", m (l 1 <@@> l 2), " of two languages ", m (l 1), and, m (l 2), " is the following language"]
  ma $ (l 1 <@@> l 2) === setcmpr (ss 1 <@> ss 2) (cs [ss 1 ∈ l 1, ss 2 ∈ l 2])

  where
    l n = clan !: n
    ss n = cstr !: n

concatenationAssociative :: Note
concatenationAssociative = thm $ do
  s [the, concatenation, " of languages is ", associative]

  toprove

concatenationNotCommutative :: Note
concatenationNotCommutative = thm $ do
  s [the, concatenation, " of languages is ", emph "not", " ", commutative]

  cexneeded

selfConcatenationDefinition :: Note
selfConcatenationDefinition = de $ do
  s [the, concatenation, " of a ", language, " ", m clan, " with itself ", m n, " times is denoted as ", m (clan ^@: n)]
  s [m (clan ^@: 0), " is defined as ", m (setof cestr)]
  ma $ clan ^@: n === (clan <@@> (clan ^@: (n - 1)))
  where n = "n"

kleeneStarDefinition :: Note
kleeneStarDefinition = de $ do
  s [the, term "Kleene star", " ", m (cks clan), " of a ", language, " ", m clan, " is the union of all the concatenations of ", m clan, " with itself"]
  ma $ cks clan === setuncmp (n ∈ naturals) (clan ^@: n)
  where n = "n"

languagePlusDefinition :: Note
languagePlusDefinition = de $ do
  s [m (clp clan), " is defined as ", m (clan <@@> cks clan)]

languesOverAlphabetDefinition :: Note
languesOverAlphabetDefinition = de $ do
  s ["The set of all languages over an alphabet ", m calph, " is denoted as follows"]
  ma $ cls === powset cstrs

infiniteLanguagesCountable :: Note
infiniteLanguagesCountable = thm $ do
  s ["Infinite languages are countable"]
  refneeded "countable"

  toprove

uncountablyManyLanguages :: Note
uncountablyManyLanguages = thm $ do
  s ["There are uncountably infinitely many languages over a given alphabet"]

  toprove

reverseLanguage :: Note
reverseLanguage = de $ do
  s ["The ", term "reverse language", " ", m (crlan clan), " is the language of all reverse strings of the strings in ", m clan]
  ma $ crlan clan === setcmpr (crstr cstr) (cstr ∈ clan)


