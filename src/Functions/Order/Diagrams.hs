{-# LANGUAGE MultiParamTypeClasses #-}
module Functions.Order.Diagrams where

import           Control.Monad          (forM, forM_)
import           Notes                  hiding (color, directed, not, (=:))
import           Prelude
import           Relations.Orders.Hasse
import           Text.Dot
import           Text.Dot.Class

type OrderFunction = [(Text, Text)]
type COLOR = Text

data OrderFunctionFig = OrderFunctionFig
    { offHasseDiagrams :: [(Text, HasseDiagram)]
    , offFunctions     :: [(COLOR, OrderFunction)]
    }

data OrderFunctionFigRenderConfig = OrderFunctionFigRenderConfig
    { offrcNodeConfig :: DotGen ()
    , offrcEdgeConfig :: DotGen ()
    }

normalConfig :: OrderFunctionFigRenderConfig
normalConfig = OrderFunctionFigRenderConfig (return ()) (return ())

dotsConfig :: OrderFunctionFigRenderConfig
dotsConfig = OrderFunctionFigRenderConfig (nodeDec [shape =: "point"]) (return ())

instance Graph OrderFunctionFig OrderFunctionFigRenderConfig where
    defaultGenConfig = normalConfig
    genGraph c funFig = do
        offrcNodeConfig c
        offrcEdgeConfig c
        graphDec ["nodesep" =: "0.5"]
        rankdir bottomTop
        edgeDec [arrowhead =: none]
        nis <- fmap concat $ forM (offHasseDiagrams funFig) $ \(n, h) -> cluster_ n $ do
            labelDec n
            nis <- drawHasseNodes h
            drawHasseEdges nis h
            return nis
        edgeDec [arrowhead =: normal]
        forM_ (offFunctions funFig) $ \(c, f) -> do
            edgeDec [color =: c]
            forM_ f $ drawEdge nis


orderFunctionFig :: Double -> OrderFunctionFigRenderConfig -> OrderFunctionFig -> Note
orderFunctionFig d c fig = do
    fp <- dot2tex $ graph_ directed $ genGraph c fig
    noindent
    hereFigure $ do
        packageDep_ "graphicx"
        includegraphics [KeepAspectRatio True, IGHeight (Cm d), IGWidth (CustomMeasure $ textwidth)] fp

