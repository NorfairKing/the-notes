module Titlepage (myTitlePage) where

import           Notes
import           System.Process (system)

myTitlePage :: Notes
myTitlePage = notesPart "titlepage" page

page :: Note
page = do
  liftIO $ system "git rev-parse --short HEAD > commit.tex" >> return ()
  text <- liftIO $ readFileTex "src/titlepage.tex"
  raw text
