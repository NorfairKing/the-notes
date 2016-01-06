module Macro.Code where

import           Types


minted :: Note -> Note -> Note
minted lang cont = do
    "\n"
    let f = liftL2 $ \lang cont -> TeXEnv "minted" [FixArg lang] $ "\n" <> cont
    f lang cont
    "\n"

pseudocode :: Note -> Note
pseudocode = minted "raw"

python :: Note -> Note
python = minted "python"


