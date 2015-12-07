{-# LANGUAGE QuasiQuotes #-}
module DataMining.MapReduce (
    mapReduce
  ) where

import           Notes

import           Functions.Basics.Macro

mapReduce :: Notes
mapReduce = notesPart "MapReduce" body

body :: Note
body = do
  section "MapReduce"
  mapReduceConcept
  mapReduceExamples
  mapReduceReferences

mapReduceConcept :: Note
mapReduceConcept = do
  subsection "The Concept"
  subsubsection "The problem"
  s ["The biggest problem with handling massive data sets is often not the complexity of the algorithm that we are dealing with but the fact that the data does not fit into memory"]
  s ["Secondary memory is multiple orders of magnitude slower than main memory"]
  s ["Often the data does not even fit onto one machine's hard disk"]
  s ["As a consequence, the bottleneck in a naive approach would be IO and networking."]
  s ["Random access to the data is no longer an option when handling massive data sets"]
  s ["When using an algorithm that handles streaming data, IO ceases to be the bottleneck but only untill the machine has run out of data to process in its storage"]
  s ["A new way of processing data is required"]

  subsubsection "The solution"
  s ["In a MapReduce framework, the computation is distributed accross multiple machines and the data is distributed on a distributed filesystem for those machines"]
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

  de $ s ["A ", term "map", " is a function ", m $ fun "Map" ((pars $ k ⨯ v) ^: p) ((pars $ k' ⨯ v') ^: q)]

  de $ s ["A ", term "reduce", " is a function ", m $ fun "Reduce" (k' ⨯ (v' ^: r)) ((pars $ k'' ⨯ v'') ^: ss)]

  nte $ s [m k, and, m k', " are sets of so-called ", term "key", "s", and, m v, and, m v', " are sets of so-called ", term "value", "s"]
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
mapReduceExamples = do
  subsection "Examples"
  wordCountExample

wordCountExample :: Note
wordCountExample = ex $ do
  s ["Counting the number of occurrences of every word in a large corpus of documents is the prime example of a problem that can be solved using mapreduce"]
  minted "python" wordCountMap
  minted "python" wordCountReduce

wordCountMap :: Note
wordCountMap = raw [litFile|src/DataMining/wordcountmap.py|]

wordCountReduce :: Note
wordCountReduce = raw [litFile|src/DataMining/wordcountreduce.py|]

mapReduceReferences :: Note
mapReduceReferences = nocite dataMiningMapReduceSlides

dataMiningMapReduceSlides :: Reference
dataMiningMapReduceSlides = Reference lectureSlides "data-mining-mapreduce" $
  [
    ("author", "Andreas Krause")
  , ("title", "Data Mining: Introduction")
  , ("year", "2015")
  , ("month", "September")
  , ("note", "Lecture Slides")
  ]
