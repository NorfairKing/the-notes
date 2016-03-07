module Logic.PropositionalLogic.Resolution where

import           Control.Monad                        (forM_, unless)
import           Notes                                hiding (color, directed,
                                                       not, (=:))

import           Data.Maybe                           (fromJust)
import           Prelude
import           Utils

import           Text.Dot

import           Data.List                            (find, intercalate, nub,
                                                       sort, sortBy)
import           Data.Ord                             (comparing)

import qualified Data.Text                            as T
import           Data.Text.Lazy                       (toStrict)

import           Text.Blaze                           (customAttribute, (!))
import           Text.Blaze.Html.Renderer.Text        (renderHtml)
import           Text.Blaze.Html4.Strict              (table, td, tr)
import           Text.Blaze.Html4.Strict.Attributes   (border, cellpadding,
                                                       cellspacing)
import qualified Text.Blaze.Internal

import           Logic.PropositionalLogic.Sentence
import           Logic.PropositionalLogic.TruthTables


data CNFSentence = Conjunction [Disjunction]
    deriving (Show, Eq)

instance Monoid CNFSentence where
    mempty = Conjunction []
    mappend (Conjunction s1) (Conjunction s2) = Conjunction $ s1 ++ s2

data Disjunction = Disjunct [CNFLit]
    deriving (Eq)

instance Show Disjunction where
    show (Disjunct ls) = intercalate " ∧ " $ map show ls

instance Ord Disjunction where
    compare (Disjunct ls1) (Disjunct ls2) = compare (length ls1) (length ls2)

instance Monoid Disjunction where
    mempty = Disjunct []
    mappend (Disjunct s1) (Disjunct s2) = Disjunct $ s1 ++ s2

data CNFLit = JustLit Text
            | NotLit Text
    deriving (Eq)

instance Ord CNFLit where
    compare = comparing textOfLit
      where
        textOfLit (JustLit t) = t
        textOfLit (NotLit t) = t

instance Show CNFLit where
    show (JustLit t) = T.unpack t
    show (NotLit t) = "¬" ++ T.unpack t

fromSentence :: Sentence -> CNFSentence
fromSentence = go . cnfTransform
  where
    go :: Sentence -> CNFSentence
    go s@(Literal _)    = Conjunction $ [go2 s]
    go s@(Or _ _)       = Conjunction $ [go2 s]
    go s@(Not _)        = Conjunction $ [go2 s]
    go (And s1 s2)      = go s1 `mappend` go s2
    go _ = error "CNF transformation didn't result in a CNF sentence."

    go2 :: Sentence -> Disjunction
    go2 (Literal (Lit True)) = Disjunct [JustLit "T", NotLit "T"] -- Something that works. In practice this won't be necessary.
    go2 (Literal (Lit False)) = Disjunct []
    go2 (Literal (Symbol s)) = Disjunct [JustLit s]
    go2 (Not (Literal (Symbol s))) = Disjunct [NotLit s]
    go2 (Or s1 s2)  = go2 s1 `mappend` go2 s2
    go2 _ = error "CNF transformation didn't result in a CNF sentence."

disjunctNode :: [Attribute] -> Disjunction -> DotGen NodeId
disjunctNode as (Disjunct []) = namelessNode $ [color =: "red", label =: tableCells ["False"]] ++ as
disjunctNode as (Disjunct ls) = namelessNode $ label =: (tableCells $ map show $ sort ls) : as

tableCells :: [String] -> Text
tableCells ls = toStrict $ renderHtml $ table' $ tr $ forM_ ls $ \l -> td $ fromString $ l
  where
    cellborder :: Text.Blaze.Internal.AttributeValue -> Text.Blaze.Internal.Attribute
    cellborder = customAttribute "cellborder"

    table' = table ! border "0" ! cellborder "1" ! cellspacing "0" ! cellpadding "5"

proofFig :: Note -> Double -> DotGraph -> Note
proofFig cap height g = do
    fp <- dot2tex g
    noindent
    hereFigure $ do
        packageDep_ "graphicx"
        includegraphics [KeepAspectRatio True, IGHeight (Cm height), IGWidth (CustomMeasure $ textwidth)] fp
        caption cap

proofUnsatisfiable :: Double -> [Sentence] -> Sentence -> Note
proofUnsatisfiable height kb query = do
    proofFig cap height $ proofGraph kb query
  where cap = do
            "A diagram of the proof of "
            m $ renderSentence query

proofGraph :: [Sentence] -> Sentence -> DotGraph
proofGraph kb query = graph_ directed $ proofGraphGen cnfSen
  where cnfSen = mconcat $ fromSentence (Not query) : map fromSentence kb

proofGraphGen :: CNFSentence -> DotGen ()
proofGraphGen (Conjunction ds) = do
    nodeDec [shape =: none]
    rankdir leftRight
    ids <- mapM (disjunctNode [color =: "green"]) $ map simplify ds
    go [] $ zip ids ds
  where
    go :: [NodeId] -> [(NodeId, Disjunction)] -> DotGen ()
    go _ [] = return ()
    go _ [(_, Disjunct [])] = return ()
    go ts ds = do
        case find (\(n, d) -> justTrue d && notElem n ts) ds of
            Just (n, _) -> do
                n' <- node "true"
                n --> n'
                go (n:ts) ds
            Nothing -> do
                let isNew (_, d1) (_, d2) =
                        case simplify `fmap` resolve d1 d2 of
                            Nothing -> False
                            Just d3 -> not (justTrue d3) && (notElem d3 $ map snd ds)
                case find (uncurry isNew) cp of
                    Nothing -> return ()
                    Just ((n1, d1), (n2, d2)) -> do
                        let d3 = simplify $ fromJust $ resolve d1 d2
                        n3 <- disjunctNode [] d3
                        n1 --> n3
                        n2 --> n3
                        let rest = sortBy (comparing snd) $ (n3, d3) : ds
                        unless (d3 == Disjunct []) $ go ts rest
      where
        cp :: [((NodeId, Disjunction), (NodeId, Disjunction))]
        cp = pairs ds

simplify :: Disjunction -> Disjunction
simplify (Disjunct ls) = Disjunct . sort . nub $ ls

justTrue :: Disjunction -> Bool
justTrue (Disjunct ls) = any (uncurry canReselove) cp
  where cp = pairs ls


resolve :: Disjunction -> Disjunction -> Maybe Disjunction
resolve (Disjunct d1) (Disjunct d2) =
    case find (uncurry canReselove) cp of
        Nothing -> Nothing
        Just (a, b) -> Just $ Disjunct $ filter (/= a) d1 ++ filter (/= b) d2
  where cp = crossproduct d1 d2

canReselove :: CNFLit -> CNFLit -> Bool
canReselove (JustLit s1) (NotLit s2) = s1 == s2
canReselove (NotLit s1) (JustLit s2) = s1 == s2
canReselove _ _ = False

