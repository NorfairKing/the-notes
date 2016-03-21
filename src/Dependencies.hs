module Dependencies where

import           Control.Monad  (unless)
import           Data.Maybe     (catMaybes)
import           Data.Time
import           Data.Version
import           Prelude
import           System.Exit    (ExitCode (..), die)
import           System.Info
import           System.Process (readCreateProcessWithExitCode, shell)


outputSystemInfo :: IO ()
outputSystemInfo = do
    zonedTime <- getZonedTime
    putStrLn "-------- [ System Information ] -------- "
    putStrLn $ "  date:     " ++ show zonedTime
    putStrLn $ "  OS:       " ++ os
    putStrLn $ "  Arch:     " ++ arch
    putStrLn $ "  Compiler: " ++ compilerName
    putStrLn $ "  Version:  " ++ showVersion compilerVersion
    putStrLn $ ""

checkDependencies :: IO ()
checkDependencies = do
    putStrLn "----------- [ Dependencies ] ----------- "
    missings <- checkAllDependencies
    unless (null missings) $ die $ "Cannot generate the notes:\nDependencies missing:\n" ++ unlines missings

type Dependency = IO (Maybe String)

checkAllDependencies :: IO [String]
checkAllDependencies = catMaybes <$> sequence allDependencies

allDependencies :: [Dependency]
allDependencies =
    [ commandDependency "latexmk"
    , commandDependency "pygmentize"
    , commandDependency "dot"
    ]

commandDependency :: String -> IO (Maybe String)
commandDependency command = do
    let proc = shell $ "command -v " ++ command
    (ec, out, _) <- readCreateProcessWithExitCode proc ""
    case ec of
        ExitSuccess   -> do
            putStrLn $ "dependency :  " ++ command ++ "\nfound at   :  " ++ out
            return Nothing
        ExitFailure _ -> do
            putStrLn $ "dependency :  " ++ command ++ "\nNOT FOUND\n"
            return $ Just command

