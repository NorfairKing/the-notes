module DataMining.Main where

import           DataMining.ApproximateRetrieval
import           DataMining.ExamQuestions
import           DataMining.LargeScaleLearning
import           DataMining.MapReduce
import           Notes

dataMining :: Note
dataMining = chapter "Data Mining" $ do
    mapReduceS
    approximateRetrieval
    largeScaleLearningS
    extraExamQuestions

    nocite dataMiningMapReduceSlides

dataMiningMapReduceSlides :: Reference
dataMiningMapReduceSlides = Reference lectureSlides "data-mining-mapreduce" $
    [
      ("author", "Andreas Krause")
    , ("title", "Data Mining")
    , ("year", "2015")
    , ("month", "September")
    , ("note", "Lecture Slides")
    ]

