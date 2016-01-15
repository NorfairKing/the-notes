module DataMining.Main where

import           DataMining.ApproximateRetrieval
import           DataMining.LargeScaleLearning
import           DataMining.MapReduce
import           Notes

dataMining :: Note
dataMining = chapter "Data Mining" $ do
    mapReduceS
    approximateRetrieval
    largeScaleLearningS
