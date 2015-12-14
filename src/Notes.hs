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

import           Prelude              (Bool (..), init, length, putStr,
                                       putStrLn, return)

import           Control.Monad.Reader (runReaderT)
import           Control.Monad.State  (gets, modify, runStateT)

import           Control.Monad        (when)
import           Data.List            (isPrefixOf, replicate)

runNote :: Note -> Config -> State -> IO (LaTeX, State)
runNote note conf state = runReaderT (runStateT (execLaTeXT note) state) conf

note :: String -> Note -> Note
note partname func = do
    pushPart partname

    part <- currentPart

    s <- isSelected
    when s $ do
        liftIO $ putStr $ replicate (length part * 2) ' '
        liftIO $ putStrLn partname
        func

    popPart

isSelected :: Note' Bool
isSelected = do
    part <- currentPart
    sels <- asks conf_selections
    return $ selects part sels

  where
    selects :: [String] -> [Selection] -> Bool
    selects ps ss = go ps ss False
        where
            go :: [String] -> [Selection] -> Bool -> Bool
            go _ [] b                       = b
            go ps (All:ss) _                = go ps ss True
            go ps ((Match s):ss) b          = if ps `matches` s
                                              then go ps ss True
                                              else go ps ss b
            go ps ((Ignore s):ss) True      = if ps `matches` s
                                              then go ps ss False
                                              else go ps ss True
            go ps ((Ignore _):ss) False     = go ps ss False

    matches :: [String] -> [String] -> Bool
    matches ps s = s `isPrefixOf` ps

currentPart :: Note' [String]
currentPart = gets state_currentPart

pushPart :: String -> Note
pushPart partname = modify (\s -> s { state_currentPart = state_currentPart s ++ [partname]})

popPart :: Note
popPart = modify (\s -> s { state_currentPart = init $ state_currentPart s })

