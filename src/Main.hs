module Main where

import           System.Environment   (getArgs)
import           System.Process       (system)

import           Notes
import           Utils

import           Prelude              (Maybe (..), error, map, print, return)

import           Constants
import           Header
import           Packages
import           Titlepage

import           Fields.Main
import           Functions.Main
import           Groups.Main
import           LinearAlgebra.Main
import           Logic.Main
import           MachineLearning.Main
import           Probability.Main
import           Relations.Main
import           Rings.Main
import           Sets.Main
import           Topology.Main



main :: IO ()
main = do
    args <- getArgs
    let mc = config args
    print mc
    case mc of
      Nothing -> error "Couldn't parse arguments."
      Just cf -> do
        removeIfExists mainBibFile
        t <- runNote entireDocument cf

        renderFile mainTexFile t

        _ <- liftIO $ system $ "latexmk -pdf -pdflatex=\"pdflatex -shell-escape -halt-on-error -enable-write18\" " ++ mainTexFile ++ " -jobname=" ++ outName
        return ()


config :: [String] -> Maybe Config
config args = do
  let ss = map constructSelection args
  return $ Config { conf_selections = ss }

constructSelection :: String -> Selection
constructSelection "all" = All
constructSelection s = Match s

runNote :: Note -> Config -> IO LaTeX
runNote note conf = runReaderT (execLaTeXT note) conf

entireDocument :: Note
entireDocument = do

  documentclass [oneside, FontSize (Pt 12), a4paper] book

  packages
  header

  document $ do
    myTitlePage
    tableofcontents
    renderNotes allNotes

    comm1 "bibliographystyle" "plain"
    comm1 "bibliography" "main"

    comm0 "printindex"
    comm0 "listoftodos"



allNotes :: Notes
allNotes = notes ""
  [
      logic
    , sets
    , relations
    , functions
    , groups
    , rings
    , fields
    , linearAlgebra
    , topology
    , probability
    , machineLearning
  ]

