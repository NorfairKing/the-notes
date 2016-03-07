{-# LANGUAGE MultiParamTypeClasses #-}
module Probability.BayesianNetwork.Graph where

import           Prelude

import           Notes                            hiding (directed, (=:))
import qualified Notes                            as N ((=:))

import           Control.Monad                    (forM, forM_)
import           Data.Maybe                       (fromMaybe)

import           Text.Dot
import           Text.Dot.Class

import qualified Data.Text                        as T

import           Probability.RandomVariable.Macro



data BayesNet = BayesNet
    { bayesNetNodes :: [Text]
    , bayesNetEdges :: [(Text, Text)]
    }

data BayesNetGenConfig = BayesNetGenConfig

instance Graph BayesNet BayesNetGenConfig where
    defaultGenConfig = BayesNetGenConfig
    genGraph _ bn = do
        nodeDec [width =: "0", height =: "0"] -- Nodes as small as possible
        rankdir leftRight

        nodes <- forM (bayesNetNodes bn) $ \n -> do
            nid <- node n
            return (n, nid)

        forM_ (bayesNetEdges bn) $ \(from, to) -> do
            let fromNode = fromMaybe
                 (error $ "From node not found: " ++ T.unpack from)
                 (lookup from nodes)
            let toNode = fromMaybe
                 (error $ "To node not found: " ++ T.unpack to)
                 (lookup to nodes)
            fromNode --> toNode

bnJointDistribution :: BayesNet -> Note
bnJointDistribution bn = do
    foldl (*) mempty $
        (flip map) (bayesNetNodes bn) $ \n ->
            cprobs (raw n) $ map raw $ incedents bn n

incedents :: BayesNet -> Text -> [Text]
incedents bn t = [ from | (from, to) <- bayesNetEdges bn, to == t ]

bnFig :: BayesNet -> Note
bnFig bn = do
    fp <- dot2tex $ graph_ directed $ genDefault bn
    noindent
    hereFigure $ do
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.5" <> textwidth)] fp
        caption $ m $ probs (map raw $ bayesNetNodes bn) N.=: bnJointDistribution bn

