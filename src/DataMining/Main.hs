module DataMining.Main where

import           DataMining.ApproximateRetrieval
import           DataMining.MapReduce
import           Notes

dataMining :: Note
dataMining = note "data-mining" $ do
    chapter "Data Mining"
    mapReduceS
    approximateRetrieval
