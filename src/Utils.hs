module Utils where

import           Types

import           Prelude

import           Data.Char         (toLower, toUpper)
import           Data.List         (intercalate, isSuffixOf)
import           Data.Maybe        (fromJust)

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


pluralOf :: String -> String
pluralOf s | isIrregular = fromJust $ lookup s irregulars
           | needsEs     = s ++ "es"
           | needsIes    = init s ++ "ies"
           | otherwise   = s ++ "s"
  where
    isIrregular = s `elem` (map fst irregulars)
    needsEs = any (`isSuffixOf` s) ["s","x","z","ch","sh"]
    needsIes = last s == 'y' && isConsonant (last $ init s)
    isVowel :: Char -> Bool
    isVowel = (`elem` ("aeiouy" :: String))
    isConsonant = not . isVowel

    irregulars :: [(String, String)]
    irregulars =
        [
            ("woman"      , "women")
          , ("man"        , "men")
          , ("child"      , "children")
          , ("tooth"      , "teeth")
          , ("foot"       , "feet")
          , ("person"     , "people")
          , ("leaf"       , "leaves")
          , ("mouse"      , "mice")
          , ("goose"      , "geese")
          , ("half"       , "halves")
          , ("knife"      , "knives")
          , ("wife"       , "wives")
          , ("life"       , "lives")
          , ("elf"        , "elves")
          , ("loaf"       , "loaves")
          , ("potato"     , "potatoes")
          , ("tomato"     , "tomatoes")
          , ("cactus"     , "cacti")
          , ("focus"      , "foci")
          , ("fungus"     , "fungi")
          , ("nucleus"    , "nuclei")
          , ("syllabus"   , "syllabi/syllabuses")
          , ("analysis"   , "analyses")
          , ("diagnosis"  , "diagnoses")
          , ("oasis"      , "oases")
          , ("thesis"     , "theses")
          , ("crisis"     , "crises")
          , ("phenomenon" , "phenomena")
          , ("criterion"  , "criteria")
          , ("datum"      , "data")
        ]
