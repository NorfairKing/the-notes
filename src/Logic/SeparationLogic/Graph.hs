module Logic.SeparationLogic.Graph where

import           Notes                              hiding (true, (=:))

import           Control.Monad                      (void)
import           Prelude                            (return)

import           Text.Dot

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


graphExample :: Note' FilePath
graphExample = dot2tex $ renderGraph $ do
        graph_ directed $ do
            graphDec [compound =: true]
            rankdir leftRight
            nodeDec [width =: "0", height =: "0"]

            x <- newNode
            void $ cluster "store" $ do
                nodeDec [shape =: none, width =: "0", height =: "0"]
                labelDec "Store"

                node_ x "x"
                return ()

            xh <- newNode
            void $ cluster "heap" $ do
                nodeDec [shape =: none]
                labelDec "Heap"
                node_ xh $ toStrict $ renderHtml $ do
                    table ! border "0" ! cellborder "1" ! cellspacing "0" ! cellpadding "5" $ do
                        tr $ do
                            td ! port "1" $ "3"
                            td ! port "2" $ "4"
            x --> (xh .: "1")
