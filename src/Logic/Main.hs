module Logic.Main (logic) where

import           Notes


logic :: Notes
logic = notes "logic" $
  [
    logicBasics
  ]

logicBasics :: Notes
logicBasics = notesPart "basics" logicPreamble logicBody

logicPreamble :: Note
logicPreamble = return ()

logicBody :: Note
logicBody = return ()
