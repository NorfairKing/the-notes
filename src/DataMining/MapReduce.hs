{-# LANGUAGE QuasiQuotes #-}
module DataMining.MapReduce where

import           Notes

import           Functions.Basics.Macro
import           Probability.LanguageModel.Terms

import           DataMining.MapReduce.Terms

mapReduceS :: Note
mapReduceS = section "MapReduce" $ do
    mapReduceConcept
    mapReduceExamples

mapReduceConcept :: Note
mapReduceConcept = subsection "The Concept" $ do
    subsubsection "The problem" $ do
        s ["The biggest problem with handling massive data sets is often not the complexity of the algorithm that we are dealing with but the fact that the data does not fit into memory"]
        s ["Secondary memory is multiple orders of magnitude slower than main memory"]
        s ["Often the data does not even fit onto one machine's hard disk"]
        s ["As a consequence, the bottleneck in a naive approach would be IO and networking."]
        s ["Random access to the data is no longer an option when handling massive data sets"]
        s ["When using an algorithm that handles streaming data, IO ceases to be the bottleneck but only untill the machine has run out of data to process in its storage"]
        s ["A new way of processing data is required"]

    subsubsection "The solution" $ do
        s ["In a ", mapReduce', " framework, the computation is distributed accross multiple machines and the data is distributed on a distributed filesystem for those machines"]
        s ["The concept of MapReduce is is based on three key ideas"]
        enumerate $ do
          item $ s ["Data is stored redundantly for reliability"]
          item $ s ["Computational power is moved as close as possible to the data it is trying to process"]
          item $ s ["Provide a unified programming model to simplify the massive parallelism"]

        s ["The MapReduce framework is optimised for the common use case"]
        itemize $ do
          item $ s ["Massive amounts of data"]
          item $ s ["Infrequent updates of those data"]
          item $ s ["Frequent reads of and appends to those data"]

        de $ s ["A ", defineTerm "map", " is a function ", m $ fun "Map" ((pars $ k ⨯ v) ^: p) ((pars $ k' ⨯ v') ^: q)]

        de $ s ["A ", defineTerm "reduce", " is a function ", m $ fun "Reduce" (k' ⨯ (v' ^: r)) ((pars $ k'' ⨯ v'') ^: ss)]

        nte $ s [m k, and, m k', " are sets of so-called ", defineTerm "key", "s", and, m v, and, m v', " are sets of so-called ", defineTerm "value", "s"]
        nte $ s ["In reality these functions will be implemented by a computation and can, in theory, have side-effects but for the sake of clarity and efficiency it is best to try to avoid such a situation"]

        s ["The programmer supplies both a map and a reduce function"]
        s ["The framework distributes the code and the data accross all the machines"]
        s ["The machines each run the map function over their part of the data"]
        s ["The framework then collects these data and sorts them by key before distributing it over the machines again"]
        s ["Lastly the machines run the reduce function over each set of values with the same key"]

        newline
        "It turns out that a lot of problems can be solved using this framework"


  where
    k = "K"
    k' = "K'"
    k'' = "K''"
    v = "V"
    v' = "V'"
    v'' = "V''"
    p = "p"
    q = "q"
    r = "r"
    ss = "s"

mapReduceExamples :: Note
mapReduceExamples = subsection "Examples" $ do
    wordCountExample
    mapReduce1GramMarkovModel
    mapReduceFrequentItemSets

wordCountExample :: Note
wordCountExample = ex $ do
    s ["Counting the number of occurrences of every word in a large corpus of documents is the prime example of a problem that can be solved using mapreduce"]
    python $ raw [litFile|src/DataMining/wordcountmap.py|]
    python $ raw [litFile|src/DataMining/wordcountreduce.py|]

mapReduce1GramMarkovModel :: Note
mapReduce1GramMarkovModel = ex $ do
    examq eth "Data Mining" "January 2014"

    let n = "n"
    s ["The task at hand is to estimate a ", nGramMarkovModel, " with ", m $ n =: 1, " with a ", mapReduce, " job"]
    s ["Given a list of documents, given by a list of words, the job should output, for each word in the corpus, a list of tuples where the first element is a word and the second element is the fraction of times the first word was followed by the second in the entire corpus"]

    python $ raw [litFile|src/DataMining/markovmodelmap.py|]
    python $ raw [litFile|src/DataMining/markovmodelreduce.py|]

mapReduceFrequentItemSets :: Note
mapReduceFrequentItemSets = ex $ do
    examq eth "Data Mining" "January 2013"

    let n = "n"
        k = "K"
        p = "P"
    s ["In a supermarket are ", m n, " items available"]
    s ["Given a list of transactions, a set of items that were bought together, you are tasked with finding all frequently bought itemsets with price greater than or equal to a given price ", m p]
    s ["Here, an itemset is a subset of a transaction and ", quoted "frequently bought", " is defined as ", quoted ("more than " <> m k), " where ", m k, " is given"]
    s ["You are given three functions"]
    itemize $ do
        item $ s [inlinePython "hash(s)", " returns a unique hash value for the itemset s"]
        item $ s [inlinePython "cost(s)", " returns the price of the itemset s"]
        item $ s [inlinePython "subsets(s)", " returns a list of all subsets of the set s with size greater than one"]
    s ["The ", mapReduce, " job that solves this problem should output a list of tuples of hash-values and number of occurrences of frequent itemsets with cost at least ", m p]

    python $ raw [litFile|src/DataMining/frequentitemsetsmap.py|]
    python $ raw [litFile|src/DataMining/frequentitemsetsreduce.py|]


