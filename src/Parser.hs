module Parser (getConfig) where

import           Options.Applicative
import           Prelude             (fmap, map, null, return)
import           Types

getConfig :: IO (Maybe Config)
getConfig = fmap config getArgs

config :: Args -> Maybe Config
config args = do
  let ss = map constructSelection $ args_selectionStrings args
  return Config {
      conf_selections   = ss
    , conf_visualDebug  = args_visualDebug args
    , conf_verbose      = args_verbose args
    , conf_ignoreReferenceErrors = args_ignoreReferenceErrors args
    , conf_subtitle     = if null st then Nothing else Just st
    , conf_texFileName  = args_texFileName args
    , conf_bibFileName  = args_bibFileName args
    , conf_pdfFileName  = args_pdfFileName args
    }
  where st = args_subtitle args

constructSelection :: String -> Selection
constructSelection "all" = All
constructSelection s = Match s


getArgs :: IO Args
getArgs = execParser opts
  where
    opts = info (helper <*> argParser) help
    help = fullDesc <> progDesc description
    description = "\"The Notes\" generator"


parseSelection :: Parser [String]
parseSelection = words <$> strArgument (
       metavar "SELECTION"
    <> help "The selection of parts to generate"
    <> value [])

argParser :: Parser Args
argParser = Args
    <$> parseSelection
    <*> switch
        (long "visual-debug"
            <> short 'd'
            <> help "Generate visual debug code")
    <*> switch
        (long "verbose"
            <> short 'v'
            <> help "Show latex output")
    <*> switch
        (long "ignore-reference-errors"
            <> help "Ignore reference errors, compile anyway.")
    <*> strOption
        (long "subtitle"
            <> value []
            <> metavar "SUBTITLE"
            <> help "The subtitle, usually for a preselect")
    <*> strOption
        (long "tex-name"
            <> value "main"
            <> metavar "NAME"
            <> help "The name of the temporary .tex file to generate")
    <*> strOption
        (long "bib-name"
            <> value "main"
            <> metavar "NAME"
            <> help "The name of the temporary .bib file to generate")
    <*> strOption
        (long "pdf-name"
            <> value "the-notes"
            <> metavar "NAME"
            <> help "The name of the output .pdf file to generate")
