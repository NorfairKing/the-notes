module Logic.SeparationLogic.Graph where

import           Notes                              hiding (true, (=:))

import           Control.Monad                      (forM, forM_)
import           Data.Maybe                         (fromMaybe)
import           Prelude

import           Text.Dot

import qualified Data.Text                          as T
import           Data.Text.Lazy                     (toStrict)
import           Text.Blaze                         (customAttribute, (!))
import           Text.Blaze.Html.Renderer.Text      (renderHtml)
import           Text.Blaze.Html4.Strict            (table, td, tr)
import           Text.Blaze.Html4.Strict.Attributes (border, cellpadding,
                                                     cellspacing)
import           Text.Blaze.Internal                (Attribute, AttributeValue)

port :: Text.Blaze.Internal.AttributeValue
              -> Text.Blaze.Internal.Attribute
port = customAttribute "port"
cellborder :: Text.Blaze.Internal.AttributeValue
              -> Text.Blaze.Internal.Attribute
cellborder = customAttribute "cellborder"

storeHeapFig :: [Text] -> [(Text, [Text])] -> [(Either Text (Text, Int), (Text, Int))] -> Note -> Note
storeHeapFig ss hs es cap = do
    fp <- storeHeap ss hs es
    noindent
    hereFigure $ do
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.25" <> textwidth)] fp
        caption $ cap


storeHeap :: [Text] -- ^ Store as list of variables
          -> [(Text, [Text])] -- ^ Heap as lists of consequtive locations with names
          -> [(Either Text (Text, Int), (Text, Int))] -- ^ Edges
          -> Note' FilePath
storeHeap store heap edges = dot2tex $ renderGraph $ graph_ directed $ do
    graphDec [compound =: true]
    rankdir leftRight
    nodeDec [width =: "0", height =: "0"] -- Nodes as small as possible

    storeNodes <- forM store $ \t -> do
        n <- newNode
        return (t, n)
    heapNodes <- forM heap $ \(name, ts) -> do
            n <- newNode
            return (name, (ts, n))

    let flattenedHeapNodes :: [(Text, (NodeId, Int))]
        flattenedHeapNodes = concatMap (\(name, (ts, n)) -> map (\(i, _) -> (name, (n, i))) (zip [0..] ts)) heapNodes


    cluster_ "store" $ do
        nodeDec [shape =: none, width =: "0", height =: "0"]
        labelDec "Store"

        forM_ storeNodes $ \(t, n) -> do
            node_ n t


    cluster_ "heap" $ do
        nodeDec [shape =: none]
        labelDec "Heap"

        forM_ heapNodes $ \(_, (ts, n)) -> do
            node_ n $ toStrict $ renderHtml $ do
                table ! border "0" ! cellborder "1" ! cellspacing "0" ! cellpadding "5" $ do
                    tr $ do
                        forM_ (zip [0..] ts) $ \(i, t) -> do
                            td ! port (fromString $ show (i :: Int)) $ (fromString $ T.unpack t)

    forM_ edges $ \(etti, (t, p)) -> do
        let fromNode = case etti of
                        Left st -> fromMaybe (error $ "Node not found: " ++ T.unpack st) (lookup st storeNodes)
                        Right (hn, hp) -> case lookup hn flattenedHeapNodes of
                                            Nothing -> error $ "Node not found: " ++ T.unpack hn ++ ":" ++ show hp
                                            Just (n, port) -> n .: (T.pack $ show port)
        let toNode = case lookup t flattenedHeapNodes of
                        Nothing -> error $ "Node not found: " ++ T.unpack t ++ ":" ++ show t
                        Just (n, _) -> n .: (T.pack $ show p)

        fromNode --> toNode
    return ()




