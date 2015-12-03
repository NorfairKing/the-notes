module Titlepage (myTitlePage) where

import           Control.Monad  (void)
import           Notes
import           System.Process (system)

myTitlePage :: Note
myTitlePage = do
  liftIO $ void $ system "git rev-parse --short HEAD > commit.tex"
  text <- liftIO $ readFileTex "src/titlepage.tex"
  raw text
