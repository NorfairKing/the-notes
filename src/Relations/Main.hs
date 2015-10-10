module Relations.Main (relations) where

import           Notes

import           Relations.Basics



relations :: Notes
relations = notes "relations" $
  [
    header
  , relationBasics
  ]

header :: Notes
header = notesPart "header" (chapter "Relations")

