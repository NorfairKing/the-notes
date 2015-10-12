module Constants where

import           Types

mainName :: String
mainName = "main"

outName :: String
outName = "the-notes"

mainTexFile :: FilePath
mainTexFile = mainName ++ ".tex"

mainBibFile :: FilePath
mainBibFile = mainName ++ ".bib"
