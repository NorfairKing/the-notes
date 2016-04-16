module Preface where

import           Notes

import           Utils

myPreface :: Note
myPreface = slow $ do
    comm1 "section*" "Preface"
    s ["These are my notes"]
    s ["There are many like them but these ones are mine"]
    newline

    s ["If you find any errors in these notes, I kindly requests you to report them"]
    newline

    s ["If there is any part of the defined notation that you do not like, you can request a copy with a modified notation"]
    s ["Thanks to the way these notes are written, changing any notation is a five minute task"]
