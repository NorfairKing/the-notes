module Main where

import           Header
import           Logic.Main
import           Notes
import           Packages
import           Probability.Main
import           Sets.Main
import           System.Environment (getArgs)
import           System.Process     (system)
import           Titlepage

main :: IO ()
main = do
    args <- getArgs
    let mc = config args
    print mc
    case mc of
      Nothing -> error "Couldn't parse arguments."
      Just cf -> do
        t <- runNote entireDocument cf

        renderFile "main.tex" t
        --let s = prettyLaTeX t
        --writeFile "main.tex" s

        liftIO $ system $ "latexmk -pdf -pdflatex=\"pdflatex -shell-escape -halt-on-error -enable-write18\" main.tex -jobname=notes"
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
    , probability
  ]

