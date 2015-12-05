module Functions.Main (functions) where

import           Notes

import           Functions.Basics          (functionBasics)
import           Functions.BinaryOperation
import           Functions.Distances
import           Functions.Order           (order)


functions :: Notes
functions = notes "functions"
  [
    header
  , functionBasics
  , binaryOperations
  , order
  , distances
  ]

header :: Notes
header = notesPart "header" (chapter "Functions")

