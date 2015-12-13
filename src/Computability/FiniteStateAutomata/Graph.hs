module Computability.FiniteStateAutomata.Graph where

import           Notes         hiding (label, true, (=:))

import           Prelude

import           Control.Monad (forM, forM_, when)
import           Data.Maybe    (fromMaybe, isNothing)

import           Text.Dot

import qualified Data.Text     as T

fsaFig :: [Text] -- ^ Set of states
          -> Text -- Initial state
          -> [Text] -- Accepting states
          -> [(Text, Text, Text)] -- ^ Edges: From, To, Symbol(s)
          -> Note -- ^ Caption
          -> Note
fsaFig states initial accepting edges cap = do
    fp <- fsaGraph states initial accepting edges
    noindent
    hereFigure $ do
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.5" <> textwidth)] fp
        caption cap

-- | A FSA graph
--
-- Warning: make sure that states are distinct.
fsaGraph :: [Text] -- ^ Set of states
          -> Text -- Initial state
          -> [Text] -- Accepting states
          -> [(Text, Text, Text)] -- ^ Edges: From, To, Symbol(s)
          -> Note' FilePath
fsaGraph states initial accepting edges = dot2tex $ renderGraph $ graph_ directed $ do
    nodeDec [width =: "0", height =: "0"] -- Nodes as small as possible
    rankdir leftRight

    stateNodes <- forM states $ \s -> do
        n <- newNode
        genNode n $
            if s `elem` accepting
                then [label =: s, shape =: "doublecircle"]
                else [label =: s]
        return (s, n)

    -- Check that accepting states are actually states
    forM_ accepting $ \s -> do
        when
            (isNothing $ lookup s stateNodes)
            (error $ "Accepting state is not in the set of states: " ++ T.unpack s)

    case lookup initial stateNodes of
        Nothing -> error "Initial state is not in the set of states" -- FIXME(kerckhove) better error locality.
        Just initialNode -> do
            n <- newNode
            genNode n ["style" =: "invis"]
            n --> initialNode

    forM_ edges $ \(from, to, symbol) -> do
        let fromNode = fromMaybe
                        (error $ "From node not found: " ++ T.unpack from)
                        (lookup from stateNodes)
        let toNode = fromMaybe
                        (error $ "To node not found: " ++ T.unpack to)
                        (lookup to stateNodes)
        genEdge fromNode toNode [label =: symbol]












