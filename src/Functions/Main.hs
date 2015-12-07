module Functions.Main (functions) where

import           Notes

import           Functions.Application     (application)
import           Functions.Basics          (basics)
import           Functions.BinaryOperation (binaryOperations)
import           Functions.Distances       (distances)
import           Functions.Order           (order)


functions :: Notes
functions = notes "functions"
  [
    header
  , basics
  , application
  , binaryOperations
  , order
  , distances
  ]

header :: Notes
header = notesPart "header" (chapter "Functions")

