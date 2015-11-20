module Main where

import           System.Exit              (exitFailure)
import           System.Process           (system)

import           Notes
import           Utils

import           Text.LaTeX.Base.Warnings

import qualified Data.Text                as T

import           Prelude                  (Bool (..), appendFile, error, filter,
                                           print, return)

import           Constants
import           Header
import           Packages
import           Parser
import           Titlepage

import           Computability.Main
import           DataMining.Main
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
    mc <- getConfig
    print mc
    case mc of
      Nothing -> error "Couldn't parse arguments."
      Just cf -> do
        removeIfExists mainBibFile
        (t, endState) <- runNote entireDocument cf startState

        case surpressWarnings (check checkAll t) of
          [] -> do
              renderFile mainTexFile t

              appendFile mainBibFile $ showReferences $ state_refs endState

              _ <- liftIO $ system $ "latexmk -pdf -pdflatex=\"pdflatex -shell-escape -halt-on-error -enable-write18\" " ++ mainTexFile ++ " -jobname=" ++ outName
              return ()
          ws -> do
              print ws
              exitFailure


surpressWarnings :: [Warning] -> [Warning]
surpressWarnings = filter leave
  where
    leave :: Warning -> Bool
    leave (UnusedLabel _) = False
    leave _ = True

startState :: State
startState = State {
    state_refs = []
  }

renderConfig :: Note
renderConfig = do
  vspace $ Cm 1
  conf <- ask
  "The code for this pdf was generated by running the `the notes' generator with the following configuration."
  verbatim $ T.pack $ show conf
  raw "\n"
  newpage


entireDocument :: Note
entireDocument = do

  documentclass [oneside, FontSize (Pt 12), a4paper] book

  packages
  header

  document $ do
    myTitlePage
    tableofcontents
    renderConfig
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
    , computability
    , probability
    , machineLearning
    , dataMining
  ]

