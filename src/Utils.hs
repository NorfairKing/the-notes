module Utils where

import           Types

import           Prelude           (Char, otherwise, return)

import           Control.Exception
import           System.Directory  (removeFile)
import           System.IO.Error   (isDoesNotExistError)

removeIfExists :: FilePath -> IO ()
removeIfExists fileName = removeFile fileName `catch` handleExists
  where handleExists e
          | isDoesNotExistError e = return ()
          | otherwise = throwIO e

split :: String -> [String]
split = splitOn '.'


splitOn :: Char -> String -> [String]
splitOn c s = go s []
  where
    go :: String -> String -> [String]
    go [] s = [s]
    go (sc:ss) acc | sc == c   = acc : go [] ss
                   | otherwise = go ss (acc ++ [sc])
