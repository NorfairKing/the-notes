module TH.Command where

import           Prelude

import           Language.Haskell.TH
import           System.Process      (readProcess)

embedOutput :: String -> Q Exp
embedOutput str = do
    out <- runIO $ readProcess cmd args "" -- input
    return $ LitE . StringL $ out
  where (cmd:args) = words str

commitHash :: Q Exp
commitHash = embedOutput "git rev-parse HEAD"

