module Notes (
    module Types
  , module Notes
  , module Macro
  , module Reference

  , modify
  ) where

import           Types

import           Constants
import           Macro
import           Reference

import           Prelude              (appendFile, concatMap, filter, foldl,
                                       map, mapM_, putStrLn, sequence_)

import           Control.Monad.Reader (MonadReader (..), ReaderT, ask, asks,
                                       runReaderT)
import           Control.Monad.State  (MonadState (..), StateT, get, gets, put,
                                       runStateT)


import           Control.Monad.Reader (MonadReader (..), ReaderT, ask, asks,
                                       runReaderT)
import           Control.Monad.State  (MonadState (..), StateT, get, gets,
                                       modify, put, runStateT)


import           Data.List            (isPrefixOf, union)

runNote :: Note -> Config -> State -> IO (LaTeX, State)
runNote note conf state = runReaderT (runStateT (execLaTeXT note) state) conf

renderNotes :: Notes -> Note
renderNotes notes = do
  selection <- asks conf_selections
  renderParts $ selectParts selection $ flattenNotes notes

selectParts :: [Selection] -> [Part] -> [Part]
selectParts [] ps = ps
selectParts ss ps = un $ map (applySelection ps) ss

un :: Eq a => [[a]] -> [a]
un = foldl union []

applySelection :: [Part] -> Selection -> [Part]
applySelection ps All = ps
applySelection ps (Match s) = filter (\(Part name _) -> s `isPrefixOf` name) ps

flattenNotes :: Notes -> [Part]
flattenNotes = go ""
  where
    go path (NotesPart name nt) = [Part (path <.> name) nt]
    go path (NotesPartList name ds) = concatMap (go $ path <.> name) ds

    (<.>) :: String -> String -> String
    [] <.> s = s
    s1 <.> s2 = s1 ++ "." ++ s2

renderParts :: [Part] -> Note
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

item :: Note -> Note
item n = comm0 "item" <> n


(<=) :: Note -> Note -> Note
(<=) = (<=:)
