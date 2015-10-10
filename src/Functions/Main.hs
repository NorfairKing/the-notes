module Functions.Main (functions) where

import           Notes

import           Functions.Basics
import           Functions.Distances


functions :: Notes
functions = notes "functions" $
  [
    header
  , functionBasics
  , distances
  ]

header :: Notes
header = notesPart "header" (chapter "Functions")

