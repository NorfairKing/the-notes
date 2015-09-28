module Notes (
    module Types
  , module Notes
  , module Macro
  ) where

import           Macro
import           Types

renderNotes :: Notes -> LaTeXT_ IO
renderNotes notes = renderParts $ flattenNotes notes

flattenNotes :: Notes -> [Part]
flattenNotes = go ""
  where
    go path (NotesPart name nt) = [Part (path <.> name) nt]
    go path (NotesPartList name ds) = concatMap (go $ path <.> name) ds

    (<.>) :: String -> String -> String
    s1 <.> s2 = s1 ++ "." ++ s2

renderParts :: [Part] -> LaTeXT_ IO
renderParts ps = do
    liftIO $ putStrLn "\nBuilding parts:"
    liftIO $ mapM_ putStrLn $ map (\(Part name _) -> name) ps
    liftIO $ putStrLn ""


    sequence_ $ map (\(Part _ body) -> body) ps


boxed :: Note -> Note
boxed n = raw "\\text{\\fboxsep=.2em\\fbox{\\m@th$\\displaystyle" <> n <> "$}}"

bla :: Note
bla = boxed leftArrow

bra :: Note
bra = boxed rightArrow
