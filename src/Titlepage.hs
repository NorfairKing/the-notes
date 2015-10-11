module Titlepage (myTitlePage) where

import           Notes
import           Prelude        (return, (>>))
import           System.Process (system)

myTitlePage :: Note
myTitlePage = do
  liftIO $ system "git rev-parse --short HEAD > commit.tex" >> return ()
  text <- liftIO $ readFileTex "src/titlepage.tex"
  raw text
