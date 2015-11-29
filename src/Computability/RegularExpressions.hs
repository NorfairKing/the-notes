module Computability.RegularExpressions (
      regularExpressions

    , regularExpression           , regularExpression_
    , languageOfARegularExpression, languageOfARegularExpression_
    , regular                     , regular_
  ) where

import           Notes

import           Computability.Languages (language)
import           Computability.Symbols   (alphabet, string)

import           Sets.Basics             (set)

makeDefs ["regular expression", "language of a regular expression", "regular"]

regularExpressions :: Notes
regularExpressions = notesPart "regular-expressions" body

body :: Note
body = do
    section "Regular Expressions"

    regularExpressionDefinition
    regularExpressionsOverAlphabet
    languageOfRegularExpression
    regularLanguageDefinition
    regularExpressionFiniteCriterium
    regularLanguagesDefinition
    reglanSubalgebra
    finiteLanguageRegular
    oneMoreStringRegular
    thereExistNonRegularLanguages
    reverseLanguageRegular

regularExpressionDefinition :: Note
regularExpressionDefinition = de $ do
    s ["A ", regularExpression', " (", term "RE", ") over an ", alphabet, " ", m calph, " is inductively defined as an expression of the following form"]
    itemize $ do
      item $ m $ cree
      item $ m $ crep
      item $ m $ "a" <> text " with " <> "a" ∈ calph
      item $ m $ e_ 1 <@@@> e_ 2
      item $ m $ e_ 1 <@|@> e_ 2
      item $ m $ crea e
    s ["Here, ", m (cs [e, e_ 1, e_ 2]), " must be regular expressions"]
  where
    e = cre
    e_ n = e !: n

regularExpressionsOverAlphabet :: Note
regularExpressionsOverAlphabet = de $ do
    s [the, set, " of ", regularExpression, "s over an ", alphabet, " ", m calph, " is denoted as ", m cres]

languageOfRegularExpression :: Note
languageOfRegularExpression = de $ do
      lab languageOfARegularExpressionDefinitionLabel
      s [the, languageOfARegularExpression', " ", m clore, " is inductively defined as follows"]

      hereFigure $ linedTable
        [cre, clre cre]
        [
          [cree, cestr]
        , [crep, emptyset]
        , ["a" <> text " with " <> "a" ∈ calph, setof "a"]
        , [e_ 1 <@@@> e_ 2, clre (e_ 1) <@@> clre (e_ 2)]
        , [e_ 1 <@|@> e_ 2, clre (e_ 1) ∪ clre (e_ 2)]
        , [crea e, cks (clre e)]
        ]

  where
    e = cre
    e_ n = e !: n

regularLanguageDefinition :: Note
regularLanguageDefinition = de $ do
    lab regularDefinitionLabel
    s ["A ", language, " is called ", regular', " if it is the ", language, " of a ", regularExpression]

regularExpressionFiniteCriterium :: Note
regularExpressionFiniteCriterium = do
  thm $ do
    s ["If a ", regularExpression, " does not contain an asterisk, its ", language, " is finite"]

    toprove

  cex $ do
    s ["The inverse of this theorem does not hold"]
    s [m (clre $ crea cree), " is a counter example"]

regularLanguagesDefinition :: Note
regularLanguagesDefinition = de $ do
  s [the, set, " of all ", regular, " languages is denoted as ", m creglan]

reglanSubalgebra :: Note
reglanSubalgebra = de $ do
  s [m creglan, " is a subalgebra of ", m cls]
  refneeded "subalgebra"

  toprove

finiteLanguageRegular :: Note
finiteLanguageRegular = thm $ do
  s ["Every finite ", language, is, regular]

  toprove

oneMoreStringRegular :: Note
oneMoreStringRegular = thm $ do
  s ["Let ", m clan, " be a ", language, and, m cstr, " be a ", string, " over the same ", alphabet, " ", m calph]
  s [m (clan ∪ setof cstr), is, regular]

  toprove

thereExistNonRegularLanguages :: Note
thereExistNonRegularLanguages = thm $ do
  s ["There exist non ", regular, " languages"]

  toprove


reverseLanguageRegular :: Note
reverseLanguageRegular = thm $ do
  s ["For any ", language, " ", m clan, " ", m (crlan clan), is, regular]

  toprove