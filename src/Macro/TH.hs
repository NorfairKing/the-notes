module Macro.TH where

import           Language.Haskell.TH
import           Language.Haskell.TH.Quote

import           Prelude                   (return)
import           Types

literally :: String -> Q Exp
literally = return . LitE . StringL

lit :: QuasiQuoter
lit = QuasiQuoter { quoteExp = literally }

litFile :: QuasiQuoter
litFile = quoteFile lit
