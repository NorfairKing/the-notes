module Probability.BayesianNetwork where

import           Notes

import           Probability.ConditionalProbability.Macro
import           Probability.Independence.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.RandomVariable.Macro
import           Probability.RandomVariable.Terms

import           Probability.BayesianNetwork.Graph
import           Probability.BayesianNetwork.Terms

bayesianNetworkS :: Note
bayesianNetworkS = section "Bayesian Networks" $ do
    bayesianNetworkDefinition
    bayesianNetworkExamples

bayesianNetworkDefinition :: Note
bayesianNetworkDefinition = de $ do
    lab bayesianNetworkDefinitionLabel
    s ["A", bayesianNetwork', "is a", directed, acyclic, graph, "that defines a joint distribution of", randomVariables, "and encodes independences and conditional independences as such."]
    todo "This should be defined way more rigorously"

bayesianNetworkExamples :: Note
bayesianNetworkExamples = do
    ex $ do
        bnFig $ BayesNet
            { bayesNetNodes = ["A", "B", "C"]
            , bayesNetEdges = [("A", "B"), ("B", "C")]
            }
    let [a, b, c] = ["A", "B", "C"]
    s ["Note that", m a, and, m c, "are", conditionallyIndependent, "given", m b]
    aligneqs (cprobss [a, c] [b])
        [ (prob a * cprob b a * cprob c b) /: prob b
        , cprob a b * cprob c b
        ]
    ex $ do
        bnFig $ BayesNet
            { bayesNetNodes = ["A", "B", "C"]
            , bayesNetEdges = [("B", "A"), ("B", "C")]
            }
    let [a, b, c] = ["A", "B", "C"]
    s ["Note that", m a, and, m c, "are", conditionallyIndependent, "given", m b]
    aligneqs (cprobss [a, c] [b])
        [ (cprob a b * prob b * cprob c b) /: prob b
        , cprob a b * cprob c b
        ]
    ex $ do
        bnFig $ BayesNet
            { bayesNetNodes = ["A", "B", "C"]
            , bayesNetEdges = [("A", "B"), ("C", "B")]
            }
    s ["Note that ", m a, and, m c, "are", independent, "but not", conditionallyIndependent, "given", m b]
    aligneqs (cprob a c)
        [ probs [a, b, c] /: cprobs b [a, c]
        , probs [a, c]
        ]
    aligneqs (cprobss [a, c] [b])
        [ (prob a * cprobs b [a, c] * prob c) /: prob b
        , (prob a * probs [a, b] * cprobs b [a, c] * prob c) /: (prob b * probs [a, b])
        , (prob a * cprob a b * cprobs b [a, c] * prob c * probs [c, b]) /: (probs [a, b] * probs [c, b])
        , (cprob a b * cprobs b [a, c] * prob c * probs [c, b]) /: (cprob b a * probs [c, b])
        , (cprob a b * cprob b c * cprobs b [a, c] * prob c * prob b) /: (cprob b a * probs [c, b])
        , (cprob a b * cprob b c) * (cprobs b [a, c] * prob b) /: (cprob b a * cprob b c)
        ]
    ex $ do
        bnFig $ BayesNet
            { bayesNetNodes = ["A", "B", "C", "D", "E"]
            , bayesNetEdges = [("A", "C"), ("B", "C"), ("C", "D"), ("C", "E")]
            }
