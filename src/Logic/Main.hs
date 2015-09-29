module Logic.Main (logic) where

import           Notes


logic :: Notes
logic = notes "logic" $
  [
    logicBasics
  ]

logicBasics :: Notes
logicBasics = notesPart "basics" logicBody

logicBody :: Note
logicBody = return ()
