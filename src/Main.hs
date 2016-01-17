module Main where

import           Prelude              as P

import qualified Data.Text            as T

import           Control.Monad.Reader (asks)
import           System.Directory     (setCurrentDirectory)
import           System.Exit          (ExitCode (..), die)
import           System.Process       (CreateProcess (..),
                                       readCreateProcessWithExitCode, shell)
import           Utils

import           Notes

import           Config
import           Header
import           License
import           Packages
import           Parser
import           Titlepage

import           Computability.Main
import           DataMining.Main
import           Fields.Main
import           Functions.Main
import           Geometry.Main
import           Groups.Main
import           LinearAlgebra.Main
import           Logic.Main
import           MachineLearning.Main
import           Probability.Main
import           Relations.Main
import           Rings.Main
import           Sets.Main
import           Statistics.Main
import           Topology.Main


main :: IO ()
main = do
    mc <- getConfig
    case mc of
        Nothing -> error "Couldn't parse arguments."
        Just cf -> do
            let gconf = defaultGenerationConfig {
                  generationSelection = conf_selection cf
                }
            let pconf = defaultProjectConfig {
                  projectGenerationConfig = gconf
                , projectTexFileName = conf_texFileName cf
                , projectBibFileName = conf_bibFileName cf
                }

            let dir = conf_tempDir cf
            makeDir dir
            setCurrentDirectory dir


            -- This is where the magic happens
            (eet, _) <- buildNote entireDocument cf pconf startState

            case eet of
                Left err -> if conf_ignoreReferenceErrors cf
                            then printErrors err
                            else do
                                printErrors err
                                error "Pdf not built."
                Right () -> return ()

            (ec, out, err) <- liftIO $ readCreateProcessWithExitCode
                                        (latexMkJob cf)
                                        ""
            let outputAnyway = do
                  putStrLn out
                  putStrLn err
            case ec of
                ExitFailure _ -> do
                    outputAnyway
                    die "Compilation failed"
                ExitSuccess -> return ()

            return ()

printErrors :: [ΛError] -> IO ()
printErrors = putStr . unlines . map show

latexMkJob :: Config -> CreateProcess
latexMkJob cf = shell $ "latexmk " ++ unwords latexMkArgs
  where
    mainTexFile :: FilePath
    mainTexFile = conf_texFileName cf ++ ".tex"

    latexMkArgs :: [String]
    latexMkArgs = ["-pdf", pdfLatexArg, jobNameArg, mainTexFile]

    jobNameArg :: String
    jobNameArg = "-jobname=" ++ conf_pdfFileName cf

    pdfLatexArg :: String
    pdfLatexArg = "-pdflatex='" ++ pdfLatexCmd ++ "'"

    pdfLatexCmd :: String
    pdfLatexCmd = "pdflatex " ++ unwords pdfLatexArgs

    pdfLatexArgs :: [String]
    pdfLatexArgs = ["-shell-escape", "-halt-on-error", "-enable-write18"]


startState :: State
startState = State

entireDocument :: Note
entireDocument = do
    documentclass [oneside, a4paper] book

    packages
    makeindex
    header

    document $ do
        myTitlePage
        renderConfig
        license
        tableofcontents
        allNotes

        bibfn <- asks conf_bibFileName
        comm1 "bibliographystyle" "plain"
        comm1 "bibliography" $ raw $ T.pack bibfn

        printindex

        listoftodos


allNotes :: Note
allNotes = do
    logica
    sets
    relations
    functions
    groups
    rings
    fields
    linearAlgebra
    geometry
    topology
    computability
    probability
    statisticsC
    machineLearning
    dataMining
