module Probability.LanguageModel where

import           Notes

import           Probability.LanguageModel.Macro
import           Probability.LanguageModel.Terms

import           Probability.ConditionalProbability.Macro
import           Probability.ProbabilityMeasure.Macro

languageModels :: Note
languageModels = note "language-model" $ do
    section "Language Models"

    languageModelDefinition

    note "n-gram-markov-model" $ do
        ngramMarkovModelDefinition
        ngramMarkovModelExamples


languageModelDefinition :: Note
languageModelDefinition = de $ do
    lab languageModelDefinitionLabel
    let n = "n"
        w = ("w" !:)
    s ["A ", languageModel', " is a probability distribution over sequences of so-called words that come from some dictionary ", m dict_]
    s ["More precicely, for every ", m $ natural n, " and every ", sequence, " of words ", m $ lst (w 1) (w n), " from ", m dict_, ", the ", languageModel, " assigns some probability ", m $ prob $ lst (w 1) (w n)]

ngramMarkovModelDefinition :: Note
ngramMarkovModelDefinition = de $ do
    lab nGramMarkovModelDefinitionLabel
    let n = "n"
    s ["An ", nGramMarkovModel', " is a ", languageModel, " that assumes that any word in a sequence is independent of all but the ", m n, " previous words"]

ngramMarkovModelExamples :: Note
ngramMarkovModelExamples = ex $ do
    s ["In a ", m 1, "-gram Markov model, the probability factorizes as follows"]
    let n = "n"
        w = ("w" !:)
        beg = "BEG"
    ma $ prob (list (w 1) (w 2) (w n)) =: cprob (w 1) beg * cprob (w 2) (w 1) * dotsb * cprob (w n) (w (n - 1))
    s ["Here we defined ", m beg, " to mean ", dquoted "the beginning of the sequence/document"]
