module Macro.Code where

import           Types

import           Macro.MetaMacro


minted :: Note -> Note -> Note
minted lang cont = do
    packageDep_ "minted"
    "\n"
    let f = liftL2 $ \lang cont -> TeXEnv "minted" [FixArg lang] $ "\n" <> cont
    f lang cont
    "\n"

mintinline :: Note -> Note -> Note
mintinline lang code = do
    packageDep_ "minted"
    comm2 "mintinline" lang code

pseudocode :: Note -> Note
pseudocode = minted "raw"

code :: Note -> Note
code = pseudocode

-- Generate these with TH

python :: Note -> Note
python = minted "python"

inlinePython :: Note -> Note
inlinePython = mintinline "python"
