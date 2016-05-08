module Utils where

import           Types

import           Prelude

import           Data.Char              (toLower, toUpper)
import           Data.List              (intercalate, isSuffixOf)
import           Data.Maybe             (fromJust)

import           Control.Exception
import           Control.Monad          (unless)
import           Control.Monad.Reader   (asks)
import           Control.Monad.State    (gets, modify)
import           System.Directory       (createDirectory, removeFile)
import           System.IO.Error        (isAlreadyExistsError,
                                         isDoesNotExistError)
import           System.Process         (readProcess)
import qualified System.Random          as R (Random (..))

import qualified Crypto.Hash.MD5        as MD5
import qualified Data.ByteString        as SB
import qualified Data.ByteString.Base16 as B16
import qualified Data.ByteString.Char8  as SB8
import qualified Data.Text.Encoding     as T
import qualified Data.Text.IO           as T



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

readFileSafely :: FilePath -> IO Text
readFileSafely filename = T.readFile filename `catch` handleExists
  where handleExists e
          | isDoesNotExistError e = return ""
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


breakUp :: String -> String
breakUp = intercalate "\n" . chunk 80

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk n xs = y1 : chunk n y2
  where (y1, y2) = splitAt n xs


runCommand :: String -> IO String
runCommand str = readProcess bin args ""
  where (bin:args) = words str

-- Because it's the only good way to do it, apparently.
timeIO :: IO a -> IO (Double, a)
timeIO action = do
    start <- read <$> runCommand "date +%s%N"
    result <- action
    end <- read <$> runCommand "date +%s%N"
    return ((end - start) / (10 ^ (9 :: Integer)), result)

printTiming :: IO () -> IO ()
printTiming func = do
    (time, _) <- timeIO func
    putStrLn $ unwords ["Total:", show time, "seconds"]

-- | Indicate that a part of the notes is skippable during fast compilation
slow :: Note -> Note
slow func = do
    fast <- asks conf_fast
    unless fast func
