module Utils where

import           Types

import           Prelude

import           Data.Char         (toLower, toUpper)
import           Data.List         (intercalate)

import           Control.Exception
import           System.Directory  (createDirectory, removeFile)
import           System.IO.Error   (isAlreadyExistsError, isDoesNotExistError)

makeDir :: FilePath -> IO ()
makeDir fp = createDirectory fp `catch` handleExists
  where handleExists e
          | isAlreadyExistsError e = return ()
          | otherwise = throwIO e

removeIfExists :: FilePath -> IO ()
removeIfExists fileName = removeFile fileName `catch` handleExists
  where handleExists e
          | isDoesNotExistError e = return ()
          | otherwise = throwIO e

pairs :: [a] -> [(a,a)]
pairs [] = []
pairs as = go as $ tail as
  where
    go [] [] = []
    go _  [] = []
    go [] _  = []
    go (a:as) bss@(_:bs) = map (\b -> (a, b)) bss ++ go as bs

crossproduct :: [a] -> [b] -> [(a,b)]
crossproduct [] [] = []
crossproduct [] _  = []
crossproduct _  [] = []
crossproduct (a:as) bs = map (\b -> (a,b)) bs ++ crossproduct as bs


sanitize :: String -> String
sanitize = concatMap replaceBad
  where
    replaceBad :: Char -> String
    replaceBad '-' = " "
    replaceBad '\'' = ""
    replaceBad c = [c]

camelCase :: String -> String
camelCase str = (\(s:ss) -> toLower s : ss) $ concatMap (\(s:ss) -> toUpper s : ss) $ words str

pascalCase :: String -> String
pascalCase str = concatMap (\(s:ss) -> toUpper s : ss) $ words str

kebabCase :: String -> String
kebabCase str = intercalate "-" $ words $ map toLower str

