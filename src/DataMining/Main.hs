module DataMining.Main (
    dataMining
  ) where

import           DataMining.MapReduce
import           Notes

dataMining :: Notes
dataMining = notes "data-mining"
  [
    notesPart "header" (chapter "Data Mining")
  , mapReduce
  ]
