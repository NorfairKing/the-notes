module DataMining.ApproximateRetrieval where

import           Notes

import           Functions.Distances    (jaccardSimilarity,
                                         jaccardSimilarityDefinitionLabel)
import           Topology.MetricSpace   (pseudoMetricSpace,
                                         pseudoMetricSpaceDefinitionLabel)

import           Functions.Basics.Macro

approximateRetrieval :: Note
approximateRetrieval = note "approximate-retrieval" $ do
    section "Approximate Retrieval"

    theProblem
    nearDuplicate

theProblem :: Note
theProblem = do
    subsection "The problem"

    s ["The general problem of approximate retrieval consists of retrieving items that are similar to a given query item"]
    s ["Abstractly these items are elements of a ", pseudoMetricSpace, ref pseudoMetricSpaceDefinitionLabel]

    -- s ["We will tackle two specific problems: Nearest Neigbor and Near duplicate."]


-- curseOfDimensionality :: Note
-- curseOfDimensionality = do
--   subsection "Curse of dimensionality"
--
--   s ["Suppose we would like to find the neigbors ", m b, " of ", m 0, " with a maximum ", m (l !: infty), "-distance at most ", m (1 - epsilon), " in ", m ((ccint 0 1) ^: d)]
--   s ["Suppose we have ", m n, " data points sampled uniformly at random from ", m ((ccint 0 1) ^: d)]
--   s ["The expected number of neigbors would be ", m (n * (pars $ 1 - epsilon) ^: d)]
--   where
--     d = "D"
--     n = "N"
--     b = "B"
--     l = "l"


-- nearestNeigbor :: Note
-- nearestNeigbor = do
--   subsection "Nearest Neigbor"
--   mempty

nearDuplicate :: Note
nearDuplicate = do
    subsection "Near Duplicate Detection"
    s ["Given a set of items ", m v, " in a pseudometric space ", m toppms, " an item ", m w', " in ", m v, " and a distance ", m (e ∈ realsp), ", find all the items ", m w, " closer than ", m e, " to " , m w']

    s ["For arbitrary pseudometric spaces, this can be arbitrarily hard"]
    s ["In reality only the item space is given so we can construct our own pseudometric that coincides of what naturally 'feels' like a distance and solve the problem for that specific case"]

    localitySensitiveHashing
  where
    v = "V"
    w' = "w'"
    w = "w"
    e = epsilon

localitySensitiveHashing :: Note
localitySensitiveHashing = do
    subsubsection "Locality Sensitive Hashing"

    s ["Locality sensitive hashing is an solution approach for the problem of near duplicate detection."]
    s ["It assumes that there exists a function ", m (fun f v (binfie_ ^: d)), " that transforms an item into a vector of bits"]
    s ["The ", jaccardSimilarity, ref jaccardSimilarityDefinitionLabel, " is then used as the distance between items (after applying ", m f, ")"]
    footnote $ do
      s ["The Jaccard similarity is defined on sets, not Boolean vector spaces"]
      s ["That is not a problem because there exists a bijection from ", m (binfie_ ^: d), " to the powerset of any set with ", m d, " elements"]
      s ["In that case a ", quoted "one", " coordinate represents the presence of that element in the subsect"]

    newline

    s ["Naively, one could calculate this distance explicitly for every pair of items and declare duplicates whenever that distance is smaller than ", m epsilon]
    s ["Since this solution has a quadratic time complexity, it is infeasable for even moderately large ", m n]

    newline

    s ["If this problem was about exact duplicates then people would scream ", dquoted "Use hashfunctions!", " because it is such a great solution"]
    s ["Locality sensitive hashing builds on that sentiment but uses so-called ", term "locality sensitive hashfunction", "s instead of regular hash functions"]
    s ["The idea is that similar items should hash to similar values"]
    footnote $ s $ ["That's exactly the opposite of what you would want in cryptographic hash functions"]

  where
    n = "N"
    f = "f"
    v = "V"
    d = "D"










