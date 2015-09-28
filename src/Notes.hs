module Notes (
    module Types
  , module Notes
  , module Macro
  ) where

import           Macro
import           Types

renderNotes :: Note -> Notes -> LaTeXT_ IO
renderNotes preamble notes = renderParts preamble $ flattenNotes notes

flattenNotes :: Notes -> [Part]
flattenNotes = go ""
  where
    go path (NotesPart name nt) = [Part (path <.> name) nt]
    go path (NotesPartList name ds) = concatMap (go $ path <.> name) ds

    (<.>) :: String -> String -> String
    s1 <.> s2 = s1 ++ "." ++ s2

renderParts :: Note -> [Part] -> LaTeXT_ IO
renderParts preamble ps = do
    liftIO $ putStrLn "\nBuilding parts:"
    liftIO $ mapM_ putStrLn $ map (\(Part name _) -> name) ps
    liftIO $ putStrLn ""


    documentclass [] book
    preamble
    document $ sequence_ $ map (\(Part _ body) -> body) ps


boxed :: Note -> Note
boxed n = raw "\\text{\\fboxsep=.2em\\fbox{\\m@th$\\displaystyle" <> n <> "$}}"

bla :: Note
bla = boxed leftArrow

bra :: Note
bra = boxed rightArrow
