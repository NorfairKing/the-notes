module Functions.Main (functions) where

import           Notes

import           Functions.Application     (application)
import           Functions.Basics          (basics)
import           Functions.BinaryOperation (binaryOperations)
import           Functions.Distances       (distances)
import           Functions.Inverse         (inverseS)
import           Functions.Jections        (jectionsS)
import           Functions.Order           (order)
import           Functions.SetFunctions    (setFunctionsS)


functions :: Note
functions = chapter "Functions" $ do
    basics
    application
    jectionsS
    inverseS
    binaryOperations
    order
    distances
    setFunctionsS


