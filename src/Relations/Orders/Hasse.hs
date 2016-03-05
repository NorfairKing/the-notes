{-# LANGUAGE MultiParamTypeClasses #-}
module Relations.Orders.Hasse where

import           Control.Monad  (forM, forM_, unless)
import           Data.List      (nub)
import           Data.Maybe     (fromMaybe)
import qualified Data.Text      as T
import           Notes          hiding (directed, not, (=:))
import           Prelude
import           Safe           (headMay)
import           Text.Dot
import           Text.Dot.Class

hasseDiagram :: [Text] -> [(Text, Text)] -> HasseDiagram
hasseDiagram nodes edges = HasseDiagram
    { hasseNodes = nodes
    , hasseEdges = nub $ edges ++ map (\n -> (n, n)) nodes
    }

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
        nis <- drawNodes (hasseEdges hd)
        drawEdges nis (hasseEdges hd)
      where

        drawNodes :: [(Text, Text)] -> DotGen [(Text, NodeId)]
        drawNodes [] = return []
        drawNodes edges = do
                -- Draw new bottoms
                botNodes <-
                    ranksame $ forM bottoms $ \t -> do
                        nid <- node t
                        return (t, nid)

                -- Draw the rest
                rest <- drawNodes notBottoms
                return $ botNodes ++ rest
             where
               notBottoms = filter (\(from, _) -> notElem from bottoms) edges
               bottoms = nub [ from | (from, _) <- edges, headMay (edgesTo from) == Just (from, from)]
               edgesTo node = filter (\(_, to) -> to == node) edges

        drawEdges :: [(Text, NodeId)] -> [(Text, Text)] -> DotGen ()
        drawEdges nis edges = forM_ cleanEdges $ drawEdge nis
          where
            cleanEdges
                = filter
                  (\e@(from, to) ->
                    null
                        [ (e1, e2)
                        | e1@(f1, t1) <- edges
                        , e2@(f2, t2) <- edges
                        , e1 /= e2
                        , e1 /= e
                        , e2 /= e
                        , f1 == from
                        , to == t2
                        , t1 == f2])
                  edges

        drawEdge :: [(Text, NodeId)] -> (Text, Text) -> DotGen ()
        drawEdge nodes (from, to) = do
            let fromN = fromMaybe (error $ "from node not found: " ++ T.unpack from) $ lookup from nodes
            let toN = fromMaybe (error $ "to node not found: " ++ T.unpack to) $ lookup to nodes
            unless (fromN == toN) $ fromN --> toN


hasseFig :: Double -> HasseDiagram -> Note
hasseFig d hd = do
    fp <- dot2tex $ graph_ directed $ genDefault hd
    noindent
    hereFigure $ do
        packageDep_ "graphicx"
        includegraphics [KeepAspectRatio True, IGHeight (Cm d), IGWidth (CustomMeasure $ textwidth)] fp

