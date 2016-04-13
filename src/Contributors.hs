{-# LANGUAGE QuasiQuotes #-}
module Contributors (renderContributors) where

import           Control.Arrow                           (second)
import           Control.Monad                           (forM, unless)
import           Data.Maybe                              (catMaybes)
import qualified Data.Text                               as T
import           Prelude

import           Text.LaTeX.LambdaTeX.Part
import           Text.LaTeX.LambdaTeX.Selection.Internal (selects, split)

import           Notes

renderContributors :: Note
renderContributors = do
    selection <- λasks configSelection
    mnames <-
        forM contributors $ \(name, parts) ->
            if (any (`selects` selection) parts)
            then return $ Just name
            else return Nothing
    let names = catMaybes mnames
    unless (null names) $ do
        comm1 "section*" "Contributors"
        verbatim $ T.pack $ unlines names
        raw "\n"


type Name = String

contributors :: [(Name, [Part])]
contributors = map (second $ map (Part . map T.pack . split)) . read $ [litFile|contributors.txt|]
