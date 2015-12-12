module Computability.RegularExpressions where

import           Notes

import           Computability.Languages.Macro
import           Computability.Languages.Terms
import           Computability.Symbols.Macro
import           Computability.Symbols.Terms
import           Sets.Basics                            (set)

import           Computability.RegularExpressions.Macro
import           Computability.RegularExpressions.Terms


regularExpressions :: Notes
regularExpressions = notesPart "regular-expressions" $ do
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
    s ["A ", regularExpression', " (", term "RE", ") over an ", alphabet, " ", m alph_, " is inductively defined as an expression of the following form"]
    itemize $ do
      item $ m rees
      item $ m ree
      item $ m $ "a" <> text " with " <> "a" ∈ alph_
      item $ m $ e_ 1 <@@@> e_ 2
      item $ m $ e_ 1 <@|@> e_ 2
      item $ m $ rea e
    s ["Here, ", m (cs [e, e_ 1, e_ 2]), " must be regular expressions"]
  where
    e = re_
    e_ n = e !: n

regularExpressionsOverAlphabet :: Note
regularExpressionsOverAlphabet = de $ do
    s [the, set, " of ", regularExpression, "s over an ", alphabet, " ", m alph_, " is denoted as ", m reoa_]

languageOfRegularExpression :: Note
languageOfRegularExpression = de $ do
      lab languageOfARegularExpressionDefinitionLabel
      s [the, languageOfARegularExpression', " ", m lore, " is inductively defined as follows"]

      hereFigure $ linedTable
        [re_, lre re_]
        [
          [rees, estr]
        , [ree, emptyset]
        , ["a" <> text " with " <> "a" ∈ alph_, setof "a"]
        , [e_ 1 <@@@> e_ 2, lre (e_ 1) <@@> lre (e_ 2)]
        , [e_ 1 <@|@> e_ 2, lre (e_ 1) ∪ lre (e_ 2)]
        , [rea e, ks (lre e)]
        ]

  where
    e = re_
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
    s [m (lre $ rea ree), " is a counter example"]

regularLanguagesDefinition :: Note
regularLanguagesDefinition = de $ do
  s [the, set, " of all ", regular, " languages is denoted as ", m reglan]

reglanSubalgebra :: Note
reglanSubalgebra = de $ do
  s [m reglan, " is a subalgebra of ", m loa_]
  refneeded "subalgebra"

  toprove

finiteLanguageRegular :: Note
finiteLanguageRegular = thm $ do
  s ["Every finite ", language, is, regular]

  toprove

oneMoreStringRegular :: Note
oneMoreStringRegular = thm $ do
  s ["Let ", m lan_, " be a ", language, and, m str_, " be a ", string, " over the same ", alphabet, " ", m alph_]
  s [m (lan_ ∪ setof str_), is, regular]

  toprove

thereExistNonRegularLanguages :: Note
thereExistNonRegularLanguages = thm $ do
  s ["There exist non ", regular, " languages"]

  toprove


reverseLanguageRegular :: Note
reverseLanguageRegular = thm $ do
  s ["For any ", language, " ", m lan_, ", ", m (rlan lan_), is, regular]

  toprove
