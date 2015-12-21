module Utils where

import           Types

import           Prelude           (otherwise, return)

import           Control.Exception
import           System.Directory  (removeFile)
import           System.IO.Error   (isDoesNotExistError)

removeIfExists :: FilePath -> IO ()
removeIfExists fileName = removeFile fileName `catch` handleExists
  where handleExists e
          | isDoesNotExistError e = return ()
          | otherwise = throwIO e

