module Macro.Note where

import           Types

import           Prelude

import qualified Text.LaTeX.LambdaTeX as L (note)

import qualified Data.Text            as T
import qualified Data.Text.IO         as T


note :: Text -> Note -> Note
note partname func = do
    L.note partname $ do
        currentPart <- λgets stateCurrentPart
        let d = length $ unPart currentPart
        liftIO $ T.putStrLn $ T.replicate (2 * d) " " <> partname
        func

