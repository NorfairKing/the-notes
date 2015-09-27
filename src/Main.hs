module Main where

import           Logic.Main
import           Notes
import           Sets.Main

main :: IO ()
main = do
    t <- execLaTeXT $ renderNotes mainDocument
    renderFile "main.tex" t

mainDocument :: Notes
mainDocument = notes "notes" [logic, sets]

