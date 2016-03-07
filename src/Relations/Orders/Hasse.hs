{-# LANGUAGE MultiParamTypeClasses #-}
module Relations.Orders.Hasse where

import           Control.Monad  (forM, forM_, void)
import           Data.List      (nub)
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

drawHasseNodes :: HasseDiagram -> DotGen [(Text, NodeId)]
drawHasseNodes hd = go $ hasseEdges hd
  where
    go :: [(Text, Text)] -> DotGen [(Text, NodeId)]
    go [] = return []
    go edges = do
            -- Draw new bottoms
            botNodes <-
                ranksame $ forM bottoms $ \t -> do
                    nid <- node t
                    return (t, nid)

            -- Draw the rest
            rest <- go notBottoms
            return $ botNodes ++ rest
         where
           notBottoms = filter (\(from, _) -> notElem from bottoms) edges
           bottoms = nub [ from | (from, _) <- edges, headMay (edgesTo from) == Just (from, from)]
           edgesTo node = filter (\(_, to) -> to == node) edges

drawHasseEdges :: [(Text, NodeId)] -> HasseDiagram -> DotGen ()
drawHasseEdges nis hd = forM_ cleanEdges $ drawEdge nis
  where
    edges = (hasseEdges hd)
    cleanEdges
        = filter
          (\e@(from, to) ->
            from /= to
            &&
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

drawHasseDiagram :: HasseDiagram -> DotGen [(Text, NodeId)]
drawHasseDiagram hd = do
    rankdir bottomTop
    nis <- drawHasseNodes hd
    drawHasseEdges nis hd
    return nis

instance Graph HasseDiagram HasseDiagramGenConfig where
    defaultGenConfig = HasseDiagramGenConfig
    genGraph _ = void . drawHasseDiagram

hasseFig :: Double -> HasseDiagram -> Note
hasseFig d hd = do
    fp <- dot2tex $ graph_ directed $ genDefault hd
    noindent
    hereFigure $ do
        packageDep_ "graphicx"
        includegraphics [KeepAspectRatio True, IGHeight (Cm d), IGWidth (CustomMeasure $ textwidth)] fp

