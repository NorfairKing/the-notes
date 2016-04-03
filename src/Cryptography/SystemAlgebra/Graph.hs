{-# LANGUAGE MultiParamTypeClasses #-}
module Cryptography.SystemAlgebra.Graph where

import           Control.Monad  (forM, forM_, void)
import           Data.List      (groupBy, nub, sortBy)
import           Data.Ord       (comparing)
import qualified Data.Text      as T
import           Notes          hiding (Label, not, (=:))
import           Prelude
import           Text.Dot
import           Text.Dot.Class

type Label = Text

data System
    = System Text [Label]
    | Connected Text Text System
    | Merge System System
    | Merges [System]
    | MergeLabels [Text] Text System
    | ParComp [System]

λ :: System -> [Text]
λ (System _ ls) = ls
λ (Connected l1 l2 s) = filter (/= l1) . filter (/= l2) $ λ s
λ (Merge s1 s2) = λ s1 ++ λ s2
λ (Merges ss) = concatMap λ ss
λ (MergeLabels ls l s) = l : (filter (`notElem` ls) $ λ s)
λ (ParComp ss) = nub $ concatMap λ ss

name :: System -> Text
name (System n _) = n
name (Connected _ _ s) = name s
name (Merge _ _) = ""
name (Merges _) = ""
name (MergeLabels _ _ s) = name s
name (ParComp ss) = mconcat $ map name ss

data SystemGenConfig = SystemGenConfig

filterE :: Text -> [(Text, NodeId)] -> [(Text, NodeId)]
filterE l = filter (\(li, _) -> li /= l)

renderSystem :: System -> DotGen [(Text, NodeId)]
renderSystem (System name ls) = cluster_ name $ do
    graphDec ["label" =: name]
    nis <- mapM node ls
    return $ zip ls nis

renderSystem (MergeLabels ls l s) = do
    ns <- renderSystem s
    nl <- node l
    let lnis = (l, nl)
    let nnis = lnis:ns
    mapM_ (\li -> drawEdge nnis (li, l)) ls
    return $ lnis : filter (\(li, _) -> li `notElem` ls) ns

renderSystem s@(Merge s1 s2) = cluster_ (T.filter (/= ' ') $ name s) $ do
    nis1 <- renderSystem s1
    nis2 <- renderSystem s2
    let ns = nis1 ++ nis2
        ls = map fst ns
    if ((length $ nub ls) == (length ls))
    then return ns
    else error "Label sets of systems must be disjunct"

renderSystem s@(Merges ss) = cluster_ (T.filter (/= ' ') $ name s) $ do
    nis <- concat <$> mapM renderSystem ss
    let ls = map fst nis
    if ((length $ nub ls) == (length ls))
    then return nis
    else error "Label sets of systems must be disjunct"

renderSystem (Connected l1 l2 sys) = do
    nis <- renderSystem sys
    drawEdge nis (l1, l2)
    return $ filterE l1 $ filterE l2 nis

renderSystem sys@(ParComp syss) = cluster_ (name sys) $ do
    if (not $ allSame $ map λ syss)
    then error "Parallel composition requires that label sets are the same"
    else do
        graphDec ["label" =: name sys]
        nnis <- concat <$> mapM renderSystem syss
        let gs = groupBy (\(l1,_) (l2, _) -> l1 == l2) $ sortBy (comparing fst) nnis
        forM gs $ \ls -> do
            let n@(l, _) = head ls -- ls will not be empty because of groupBy
            newn <- node l
            forM_ ls $ \(_, li) -> li --> newn
            return n

allSame :: (Eq a) => [a] -> Bool
allSame xs = all (== head xs) (tail xs)

compose :: Text -> Text -> System -> System -> System
compose l1 l2 s1 s2 = Connected l1 l2 $ Merge s1 s2

instance Graph System SystemGenConfig where
    defaultGenConfig = SystemGenConfig
    genGraph _ sys = do
        rankdir leftRight
        void $ renderSystem sys

systemFig :: Double -> System -> Note -> Note
systemFig d sys cap = do
    fp <- dot2tex $ graph_ undirected $ genDefault sys
    noindent
    hereFigure $ do
        packageDep_ "graphicx"
        includegraphics [KeepAspectRatio True, IGHeight (Cm d), IGWidth (CustomMeasure $ textwidth)] fp
        caption cap


systemsFig :: Double -> [System] -> Note -> Note
systemsFig d syss cap = do
    (fp:fs) <- mapM genDot syss
    noindent
    hereFigure $ do
        packageDep_ "graphicx"
        graph fp
        forM_ fs $ \f -> do
            hspace (Cm 1.0)
            graph f
        caption cap
  where
    genDot = dot2tex . graph_ undirected . genDefault
    graph = includegraphics [KeepAspectRatio True, IGHeight (Cm d), IGWidth (CustomMeasure $ textwidth)]

