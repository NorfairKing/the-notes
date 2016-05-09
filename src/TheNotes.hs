module TheNotes where

import           Prelude                as P

import qualified Data.Text              as T

import           Control.DeepSeq        (force)
import           Control.Exception.Base (evaluate)
import           Control.Monad          (void)
import           Control.Monad.Reader   (asks)
import           System.Directory       (copyFile, withCurrentDirectory)
import           System.Exit            (ExitCode (..), die)
import           System.Process         (CreateProcess (..),
                                         readCreateProcessWithExitCode, shell)
import           System.Random          (mkStdGen)
import           Utils

import           Notes

import           Config
import           Contributors
import           Dependencies
import           Header
import           License
import           Packages
import           Parser
import           Preface
import           Titlepage

import           Computability.Main
import           Cryptography.Main
import           DataMining.Main
import           Fields.Main
import           FormalMethods.Main
import           Functions.Main
import           Geometry.Main
import           GraphTheory.Main
import           Groups.Main
import           LinearAlgebra.Main
import           Logic.Main
import           MachineLearning.Main
import           NumberTheory.Main
import           Probability.Main
import           ProgramAnalysis.Main
import           Relations.Main
import           Rings.Main
import           Sets.Main
import           Statistics.Main
import           Topology.Main


theNotes :: IO ()
theNotes = printTiming $ do
    printHeader
    outputSystemInfo
    checkDependencies
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

            let tmpdir = conf_tempDir cf
                outdir = conf_outDir cf
            makeDir tmpdir
            makeDir outdir
            withCurrentDirectory tmpdir $ do
                printGenerationHeader

                let mn = conf_texFileName cf ++ ".tex"

                beforeHash <- hashContent <$> (liftIO $ readFileSafely mn)
                void $ evaluate $ force beforeHash

                -- This is where the magic happens
                (eet, _) <- buildNote entireDocument cf pconf startState

                case eet of
                    Left err -> if conf_ignoreReferenceErrors cf
                                then printErrors err
                                else do
                                    printErrors err
                                    error "Pdf not built."
                    Right () -> return ()

                putStrLn ""

                afterHash <- hashContent <$> (liftIO $ readFileSafely mn)
                void $ evaluate $ force afterHash

                printCompilationHeader
                (dur, (ec, out, err)) <-
                    liftIO $ timeIO $ do
                        result <- readCreateProcessWithExitCode (latexMkJob cf) ""
                        evaluate $ force result

                if beforeHash == afterHash
                then liftIO $ putStrLn $ "LaTeX compilation was done already."
                else liftIO $ putStrLn $ unwords ["LaTeX compilation took", show dur, "seconds."]

                let outputAnyway = do
                      putStrLn out
                      putStrLn err
                case ec of
                    ExitFailure _ -> do
                        outputAnyway
                        die "Compilation failed"
                    ExitSuccess -> do
                        -- Copy output file from temp dir to output dir
                        let file = conf_pdfFileName cf ++ ".pdf"
                        copyFile file (outdir ++ "/" ++ file)
                        putStrLn "Compilation success.\n"

            return ()

printHeader :: IO ()
printHeader = do
    putStrLn "---------------- [ The Notes ] ---------------- "
    putStrLn "  by Tom Sydney Kerckhove                       "
    putStrLn "     syd.kerckhove@gmail.com                    "
    putStrLn "                                                "
    putStrLn "  at https://github.com/NorfairKing/the-notes   "
    putStrLn "     http://cs-syd.eu                           "
    putStrLn "                                                "

printGenerationHeader :: IO ()
printGenerationHeader = do
    putStrLn "------------ [ Generation ] ------------ "

printCompilationHeader :: IO ()
printCompilationHeader = do
    putStrLn "------------ [ Compilation ] ----------- "

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
startState = State { state_rng = mkStdGen 42 }

entireDocument :: Note
entireDocument = do
    documentclass [oneside, a4paper] book

    packages
    makeindex
    header

    document $ do
        slow $ do
            myTitlePage
            myPreface

            -- Ensure that pdf numbers coincide with the page numbers in the document
            comm2 "addtocounter" "page" "1"

            renderConfig
            license
            renderContributors
            tableofcontents

        allNotes

        slow $ do
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
    graphTheory
    groupsC
    rings
    fields
    linearAlgebra
    numberTheoryC
    geometry
    topology
    computability
    probability
    statisticsC
    programAnalysisC
    cryptography
    formalMethods
    machineLearning
    dataMining

