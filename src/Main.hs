module Main where

import           Header
import           Logic.Main
import           Notes
import           Packages
import           Sets.Main

main :: IO ()
main = do
    t <- execLaTeXT $ renderNotes (packages <> header) mainDocument

    renderFile "main.tex" t
    --let s = prettyLaTeX t
    --writeFile "main.tex" s


mainDocument :: Notes
mainDocument = notes "notes" $
  [
      logic
    , sets
  ]

