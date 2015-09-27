module Notes (
    module Types
  , module Notes
  , module Text.LaTeX
  , module Text.LaTeX.Packages.AMSMath
  , module Text.LaTeX.Base.Pretty
  ) where

import           Text.LaTeX
import           Text.LaTeX.Base.Class
import           Text.LaTeX.Base.Pretty
import           Text.LaTeX.Base.Syntax
import           Text.LaTeX.Packages.AMSMath
import           Text.LaTeX.Packages.AMSThm

import qualified Data.Text                   as T

import           Types

notes :: String -> [Notes] -> Notes
notes = NotesPartList

notesPart :: String ->  Note -> Note -> Notes
notesPart name preamble body = NotesPart $ Part name preamble body

renderNotes :: Notes -> LaTeXT_ IO
renderNotes notes = renderParts $ flattenNotes notes

flattenNotes :: Notes -> [Part]
flattenNotes = go ""
  where
    go path (NotesPart pt) = [pt {part_name = path <.> part_name pt} ]
    go path (NotesPartList name ds) = concatMap (go $ path <.> name) ds

    (<.>) :: String -> String -> String
    s1 <.> s2 = s1 ++ "." ++ s2

renderParts :: [Part] -> LaTeXT_ IO
renderParts ps = do
    liftIO $ putStrLn "\nBuilding parts:"
    liftIO $ mapM_ putStrLn $ map part_name ps
    liftIO $ putStrLn ""


    generalPreamble
    sequence_ $ map part_preamble ps
    document $ sequence_ $ map part_body ps


generalPreamble :: Note
generalPreamble = do
    documentclass [] book
    author "Tom Sydney Kerckhove"
    title "The Notes"

    packages
    referencesPreamble

packages :: Note
packages = do
    usepackage [] "amsmath"
    usepackage [] "mdframed"


referencesPreamble :: Note
referencesPreamble = do
    raw "\\newtheorem{thm}{Theorem}[chapter]"
    raw "\\let\\th\\undefined\n"
    newmdtheoremenv "de" "Definition"
    newmdtheoremenv "alg" "Algorithm"
    newtheorem "th" "Theorem"
    newtheorem "prop" "Property"
    newtheorem "pro" "Proposition"
    newtheorem "nte" "Note"
    newtheorem "exm" "Example"
    newtheorem "cex" "Counterexample"
    newtheorem "con" "Concequence"
    newtheorem "lem" "Lemma"

newmdtheoremenv :: LaTeXC l => String -> l -> l
newmdtheoremenv str = liftL $ \l -> TeXComm "newmdtheoremenv" [ FixArg $ fromString str , FixArg l ]

notesChapter :: Text -> Note
notesChapter title = do
  chapter $ raw title
  label . raw $ T.concat ["ch:", T.toLower title]

notesSection :: Text -> Note
notesSection title = do
  section $ raw title
  label . raw $ T.concat ["sec:", T.toLower title]

de :: Note -> Note
de = theorem "de"

environment :: String -> (Note -> Note)
environment name = liftL $ TeXEnv name []

ix :: Text -> Note
ix text = do
    index rt
    rt
  where
    rt = raw text

term :: Text -> Note
term text = do
    index rt
    textbf rt
  where
    rt = raw text

index :: Note -> Note
index = liftL $ \l -> TeXComm "index" [FixArg l]
