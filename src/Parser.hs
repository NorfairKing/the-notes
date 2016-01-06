module Parser (getConfig) where

import           Options.Applicative
import           Prelude               (null, return, (>>=))

import           System.Directory      (getCurrentDirectory)
import           System.FilePath.Posix (isAbsolute, (</>))
import           Types

getConfig :: IO (Maybe Config)
getConfig = getArgs >>= config

config :: Args -> IO (Maybe Config)
config args = do
    let ss = constructSelection $ args_selectionString args

    let tda = args_tempDir args
    tempdir <- if isAbsolute tda
                then return tda
                else do
                    dir <- getCurrentDirectory
                    return $ dir </> tda


    return $ Just $ Config {
          conf_selection                = ss
        , conf_visualDebug              = args_visualDebug args
        , conf_verbose                  = args_verbose args
        , conf_ignoreReferenceErrors    = args_ignoreReferenceErrors args
        , conf_todos                    = args_todos args
        , conf_subtitle                 = if null st then Nothing else Just st
        , conf_texFileName              = args_texFileName args
        , conf_bibFileName              = args_bibFileName args
        , conf_pdfFileName              = args_pdfFileName args
        , conf_tempDir                  = tempdir
        }
  where st = args_subtitle args

getArgs :: IO Args
getArgs = execParser opts
  where
    opts = info (helper <*> argParser) help
    help = fullDesc <> progDesc description
    description = "\"The Notes\" generator"


parseSelection :: Parser String
parseSelection = strArgument (
       metavar "SELECTION"
    <> help "The selection of parts to generate"
    <> value "all")

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
    <*> switch
        (long "todos"
            <> help "Render all todo's left in the text.")
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
    <*> strOption
        (long "tmp-dir"
            <> short 'd'
            <> value "tmp"
            <> metavar "DIR"
            <> help "The working directory for note generating")
