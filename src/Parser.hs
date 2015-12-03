module Parser (getConfig) where

import           Options.Applicative
import           Prelude             (fmap, map, return)
import           Types

getConfig :: IO (Maybe Config)
getConfig = fmap config getArgs

config :: Args -> Maybe Config
config args = do
  let ss = map constructSelection $ args_selectionStrings args
  return Config {
      conf_selections = ss
    , conf_visualDebug = args_visualDebug args
    }

constructSelection :: String -> Selection
constructSelection "all" = All
constructSelection s = Match s


getArgs :: IO Args
getArgs = execParser opts
  where
    opts = info (helper <*> argParser) help
    help = fullDesc <> progDesc description
    description = "\"The Notes\" generator"

argParser :: Parser Args
argParser = Args
    <$> parseSelection
    <*> switch (long "visual-debug"
             <> short 'd'
             <> help "Generate visual debug code")

parseSelection :: Parser [String]
parseSelection = fmap words $ strArgument (
       metavar "SELECTION"
    <> help "The selection of parts to generate"
    <> value [])
