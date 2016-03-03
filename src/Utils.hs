module Utils where

import           Types

import           Prelude

import           Data.Char              (toLower, toUpper)
import           Data.List              (intercalate, isSuffixOf)
import           Data.Maybe             (fromJust)

import           Control.Exception
import           Control.Monad.State    (gets, modify)
import           System.Directory       (createDirectory, removeFile)
import           System.IO.Error        (isAlreadyExistsError,
                                         isDoesNotExistError)
import qualified System.Random          as R (Random (..))

import qualified Crypto.Hash.MD5        as MD5
import qualified Data.ByteString        as SB
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8  as SB8
import qualified Data.Text.Encoding     as T



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
           | needsSes    = (init . init $ s) ++ "es"
           | needsEs     = s ++ "es"
           | needsIes    = init s ++ "ies"
           | otherwise   = s ++ "s"
  where
    isIrregular = s `elem` (map fst irregulars)
    needsEs = any (`isSuffixOf` s) ["s","x","z","ch","sh"]
    needsSes = "sis" `isSuffixOf` s
    needsIes = last s == 'y' && isConsonant (last $ init s)
    isVowel :: Char -> Bool
    isVowel = (`elem` ("aeiouy" :: String))
    isConsonant = not . isVowel

    irregulars :: [(String, String)]
    irregulars =
        [
            ("analysis"   , "analyses")
          , ("cactus"     , "cacti")
          , ("child"      , "children")
          , ("crisis"     , "crises")
          , ("criterion"  , "criteria")
          , ("datum"      , "data")
          , ("diagnosis"  , "diagnoses")
          , ("elf"        , "elves")
          , ("focus"      , "foci")
          , ("foot"       , "feet")
          , ("fungus"     , "fungi")
          , ("goose"      , "geese")
          , ("half"       , "halves")
          , ("knife"      , "knives")
          , ("leaf"       , "leaves")
          , ("life"       , "lives")
          , ("loaf"       , "loaves")
          , ("man"        , "men")
          , ("mouse"      , "mice")
          , ("nucleus"    , "nuclei")
          , ("oasis"      , "oases")
          , ("person"     , "people")
          , ("phenomenon" , "phenomena")
          , ("potato"     , "potatoes")
          , ("syllabus"   , "syllabi/syllabuses")
          , ("thesis"     , "theses")
          , ("tomato"     , "tomatoes")
          , ("tooth"      , "teeth")
          , ("vertex"     , "vertices")
          , ("wife"       , "wives")
          , ("woman"      , "women")
        ]

hashContent :: Text -> FilePath
hashContent = SB8.unpack . SB.take 16 . B16.encode . MD5.hash . T.encodeUtf8

random :: R.Random a => Note' a
random = do
    rng <- gets state_rng
    let (a, rng') = R.random rng
    modify $ \s -> s { state_rng = rng' }
    return a
