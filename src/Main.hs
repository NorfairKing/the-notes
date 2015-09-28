module Main where

import           Header
import           Logic.Main
import           Notes
import           Packages
import           Sets.Main
import           Titlepage

main :: IO ()
main = do
    t <- execLaTeXT $ entireDocument

    renderFile "main.tex" t
    --let s = prettyLaTeX t
    --writeFile "main.tex" s

entireDocument :: Note
entireDocument = do

  documentclass [oneside, FontSize (Pt 12), a4paper] book

  packages
  header

  document $ do
    myTitlePage
    tableofcontents
    renderNotes allNotes




allNotes :: Notes
allNotes = notes "notes" $
  [
      logic
    , sets
  ]

