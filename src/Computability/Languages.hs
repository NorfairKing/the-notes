module Computability.Languages where

import           Notes

import           Computability.Languages.Macro
import           Computability.Languages.Terms
import           Functions.BinaryOperation.Terms
import           Sets.Algebra.Union.Terms
import           Sets.Basics.Terms

import           Computability.Symbols.Macro
import           Computability.Symbols.Terms     hiding (concatenation,
                                                  concatenation',
                                                  concatenationDefinitionLabel)

languages :: Note
languages = section "Languages" $ do
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
    reverseLanguageDefinition

languageDefinition :: Note
languageDefinition = de $ do
    lab languageDefinitionLabel
    s ["A ", language', " over an ", alphabet, " ", m alph_, " is a ", set, " of finite strings over that ", alphabet]

languageConcatenationDefinition :: Note
languageConcatenationDefinition = de $ do
    lab concatenationDefinitionLabel
    s ["The ", concatenation', " ", m (l 1 <@@> l 2), " of two languages ", m (l 1), and, m (l 2), " is the following ", language]
    ma $ (l 1 <@@> l 2) === setcmpr (ss 1 <@> ss 2) (cs [ss 1 ∈ l 1, ss 2 ∈ l 2])
  where
    l n = lan_ !: n
    ss n = str_ !: n

concatenationAssociative :: Note
concatenationAssociative = thm $ do
    s [the, concatenation, " of languages is ", associative_]

    toprove

concatenationNotCommutative :: Note
concatenationNotCommutative = thm $ do
    s [the, concatenation, " of languages is ", emph "not", " ", commutative]

    cexneeded

selfConcatenationDefinition :: Note
selfConcatenationDefinition = de $ do
    s [the, concatenation, " of a ", language, " ", m lan_, " with itself ", m n, " times is denoted as ", m (lan_ ^@: n)]
    s [m (lan_ ^@: 0), " is defined as ", m (setof estr)]
    ma $ lan_ ^@: n === (lan_ <@@> (lan_ ^@: (n - 1)))
  where n = "n"

kleeneStarDefinition :: Note
kleeneStarDefinition = de $ do
    lab kleeneStarDefinitionLabel
    s [the, kleeneStar', " ", m (ks lan_), " of a ", language, " ", m lan_, " is the ", union, " of all the concatenations of ", m lan_, " with itself"]
    ma $ ks lan_ === setuncmp (n ∈ naturals) (lan_ ^@: n)
  where n = "n"

languagePlusDefinition :: Note
languagePlusDefinition = de $ do
    s [m (lp lan_), " is defined as ", m (lan_ <@@> ks lan_)]

languesOverAlphabetDefinition :: Note
languesOverAlphabetDefinition = de $ do
    s ["The ", set, " of all languages over an ", alphabet, " ", m alph_, " is denoted as follows"]
    ma $ loa_ === powset strsof_

infiniteLanguagesCountable :: Note
infiniteLanguagesCountable = thm $ do
    s ["Infinite languages are countable"]
    refneeded "countable"

    toprove

uncountablyManyLanguages :: Note
uncountablyManyLanguages = thm $ do
    s ["There are uncountably infinitely many languages over a given ", alphabet]
    refneeded "uncountably infinite"

    toprove

reverseLanguageDefinition :: Note
reverseLanguageDefinition = de $ do
    lab reverseLanguageDefinitionLabel
    s ["The ", reverseLanguage', " ", m (rlan lan_), " is the ", language, " of all reverse strings of the strings in ", m lan_]
    ma $ rlan lan_ === setcmpr (rstr str_) (str_ ∈ lan_)


