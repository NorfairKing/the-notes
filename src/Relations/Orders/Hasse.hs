{-# LANGUAGE MultiParamTypeClasses #-}
module Relations.Orders.Hasse where

import           Control.Monad  (forM, forM_, unless)
import           Data.List      (nub)
import           Data.Maybe     (fromMaybe)
import           Notes          hiding (directed, (=:))
import           Prelude
import           Text.Dot
import           Text.Dot.Class

hasseDiagram :: [(Text, Text)] -> HasseDiagram
hasseDiagram edges = HasseDiagram
    { hasseNodes = nub $ map fst e ++ map snd e
    , hasseEdges = e
    }
  where
    e = nub edges

data HasseDiagram = HasseDiagram
    { hasseNodes :: [Text]
    , hasseEdges :: [(Text, Text)]
    }

data HasseDiagramGenConfig = HasseDiagramGenConfig

-- TODO fix this drawing so that it doesn't sho unnecessary edges.
instance Graph HasseDiagram HasseDiagramGenConfig where
    defaultGenConfig = HasseDiagramGenConfig
    genGraph _ hd = do
        rankdir bottomTop
        nodes <- forM (hasseNodes hd) node
        let ns = zip (hasseNodes hd) nodes
        forM_ (hasseEdges hd) $ \(from, to) -> do
            let fromN = fromMaybe (error "from node not found") $ lookup from ns
            let toN = fromMaybe (error "from to not found") $ lookup to ns
            unless (fromN == toN) $ do
                fromN --> toN


hasseFig :: HasseDiagram -> Note
hasseFig hd = do
    fp <- dot2tex $ graph_ directed $ genDefault hd
    noindent
    hereFigure $ do
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.5" <> textwidth)] fp

