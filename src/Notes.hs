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

buildNote :: Note -> Config -> ProjectConfig -> State -> IO (Either [ΛError] (), State)
buildNote note conf λconf state = runReaderT (runStateT (buildLaTeXProject note λconf) state) conf

