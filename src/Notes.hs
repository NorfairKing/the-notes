module Notes (
    module Types
  , module Notes
  , module Macro
  , module TH
  ) where

import           Macro
import           Prelude
import           TH
import           Types

import           Control.Monad.Reader (runReaderT)
import           Control.Monad.State  (runStateT)

runNote :: Note -> Config -> ProjectConfig -> State -> IO (Either String (), State)
runNote note conf λconf state = runReaderT (runStateT (buildLaTeXProject note λconf) state) conf

