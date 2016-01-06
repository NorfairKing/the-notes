module Macro.Code where

import           Types

import           Macro.MetaMacro


minted :: Note -> Note -> Note
minted lang cont = do
    "\n"
    let f = liftL2 $ \lang cont -> TeXEnv "minted" [FixArg lang] $ "\n" <> cont
    f lang cont
    "\n"

mintinline :: Note -> Note -> Note
mintinline = comm2 "mintinline"

pseudocode :: Note -> Note
pseudocode = minted "raw"

-- Generate these with TH

python :: Note -> Note
python = minted "python"

inlinePython :: Note -> Note
inlinePython = mintinline "python"
