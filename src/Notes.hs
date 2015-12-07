module Notes (
    module Types
  , module Notes
  , module Macro
  , module Reference
  , module TH
  ) where

import           Types

import           TH

import           Macro
import           Reference

import           Prelude              (Bool (..), concatMap, filter, flip,
                                       foldl, map, mapM_, putStrLn)
import qualified Prelude              as P

import           Control.Monad.Reader (runReaderT)
import           Control.Monad.State  (runStateT)

import           Data.List            (break, head, intercalate, isPrefixOf,
                                       null, repeat, tail, union, zipWith)
import           Data.Tree            (Forest, Tree (..))

runNote :: Note -> Config -> State -> IO (LaTeX, State)
runNote note conf state = runReaderT (runStateT (execLaTeXT note) state) conf

renderNotes :: Notes -> Note
renderNotes notes = do
  selection <- asks conf_selections
  renderParts $ selectParts selection $ flattenNotes notes

selectParts :: [Selection] -> [Part] -> [Part]
selectParts ss ps = foldl (applySelection ps) [] ss

un :: Eq a => [[a]] -> [a]
un = foldl union []


applySelection :: [Part] -> [Part] -> Selection -> [Part]
applySelection global _ All = global
applySelection global ps (Match s) = ps ++ filter (matches s) global
applySelection _ ps (Ignore s) = filter (P.not . matches s) ps

matches :: String -> Part -> Bool
matches s (Part n _) = split s `isPrefixOf` split n

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
    liftIO $ putStrLn "Building parts:"
    liftIO $ putStrLn $ drawForest $ treeify ps

    mapM_ (\(Part _ body) -> body) ps

treeify :: [Part] -> Forest String
treeify [] = []
treeify [Part "" _] = []
treeify [Part n _] = [Node n []]
treeify (p@(Part n _):ps) = (Node nh $ treeify $ map losefirst (p:same)) : treeify rest
  where
    nh = head $ split n
    (same, rest) = flip break ps $ \(Part m _) ->
        let ms = split m
        in (P.not (null ms) P.&& (nh /= head ms))

losefirst :: Part -> Part
losefirst p@(Part n c) = if null ns
                       then p
                       else Part (intercalate "." $ tail ns) c
  where
    ns = split n

split :: String -> [String]
split s = go s []
  where
    go :: String -> String -> [String]
    go [] s = [s]
    go ('.':ss) acc = acc : go [] ss
    go (s:ss) acc = go ss (acc ++ [s])

drawForest :: Forest String -> String
drawForest  = unlines . map drawTree

drawTree :: Tree String -> String
drawTree  = unlines . draw

draw :: Tree String -> [String]
draw (Node x ts0) = x : drawSubTrees ts0
  where
    drawSubTrees [] = []
    drawSubTrees [t] =
        shift "└─ " "   " (draw t)
    drawSubTrees (t:ts) =
        shift "├─ " "│  " (draw t) ++ drawSubTrees ts
    shift first other = zipWith (++) (first : repeat other)

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

(>=) :: Note -> Note -> Note
(>=) = (>=:)

(>) :: Note -> Note -> Note
(>) = (>:)

(<) :: Note -> Note -> Note
(<) = (<:)
