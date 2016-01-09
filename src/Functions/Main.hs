module Functions.Main (functions) where

import           Notes

import           Functions.Application     (application)
import           Functions.Basics          (basics)
import           Functions.BinaryOperation (binaryOperations)
import           Functions.Distances       (distances)
import           Functions.Order           (order)


functions :: Note
functions = chapter "Functions" $ do
    basics
    application
    binaryOperations
    order
    distances


