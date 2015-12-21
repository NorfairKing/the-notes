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

import qualified Data.Text            as T
import qualified Data.Text.IO         as T
import qualified Text.LaTeX.LambdaTeX as L (note)

import           Control.Monad.Reader (runReaderT)
import           Control.Monad.State  (runStateT)

runNote :: Note -> Config -> ProjectConfig -> State -> IO (Either [ΛError] (), State)
runNote note conf λconf state = runReaderT (runStateT (buildLaTeXProject note λconf) state) conf


note :: Text -> Note -> Note
note partname func = do
    currentPart <- λgets stateCurrentPart
    let d = length $ unPart currentPart
    liftIO $ T.putStrLn $ T.replicate (2 * d) " " <> partname
    L.note partname func
