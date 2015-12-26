module Logic.PropositionalLogic.Resolution where

import           Control.Monad                      (forM_, unless)
import           Notes                              hiding ((=:))

import           Prelude
-- import           System.FilePath.Posix (dropExtension)
import           Data.Maybe                         (fromJust, isJust)

import           Text.Dot

import           Data.List                          (find, intercalate)
import qualified Data.Text                          as T
-- import           Logic.PropositionalLogic.Sentence
import           Data.Text.Lazy                     (toStrict)
import           Text.Blaze                         (customAttribute, (!))
import           Text.Blaze.Html.Renderer.Text      (renderHtml)
import           Text.Blaze.Html4.Strict            (table, td, tr)
import           Text.Blaze.Html4.Strict.Attributes (border, cellpadding,
                                                     cellspacing)
import           Text.Blaze.Internal                (Attribute, AttributeValue)



data CNFSentence = Conjunction [Disjunction]

data Disjunction = Disjunct [CNFLit]
    deriving (Eq)

instance Show Disjunction where
    show (Disjunct ls) = intercalate " ∧ " $ map show ls

data CNFLit = JustLit Text
            | NotLit Text
    deriving (Eq)

instance Show CNFLit where
    show (JustLit t) = T.unpack t
    show (NotLit t) = "¬" ++ T.unpack t

disjunctNode :: Disjunction -> DotGen NodeId
disjunctNode (Disjunct []) = node $ tableCells ["False"]
disjunctNode (Disjunct ls) = node $ tableCells $ map show ls

tableCells :: [String] -> Text
tableCells ls = toStrict $ renderHtml $ table' $ tr $ forM_ ls $ \l -> td $ fromString $ l
  where
    cellborder :: Text.Blaze.Internal.AttributeValue -> Text.Blaze.Internal.Attribute
    cellborder = customAttribute "cellborder"

    table' = table ! border "0" ! cellborder "1" ! cellspacing "0" ! cellpadding "5"

-- TODO(kerckhove) This doesn't actually work, it sometimes does if you're lucky. Fix that!
proofUnsatisfiable :: Note -> CNFSentence -> Note
proofUnsatisfiable cap (Conjunction ds) = dotFig cap $ graph_ directed $ do
        nodeDec [shape =: none]
        rankdir leftRight
        ids <- mapM disjunctNode ds
        go $ zip ids ds
  where
    go :: [(NodeId, Disjunction)] -> DotGen ()
    go [] = return ()
    go [(_, Disjunct [])] = return ()
    go ds =
        unless (any empty ds) $ do
            case find (justTrue . snd) ds of
                Just t@(n, _) -> do
                    n' <- node "true"
                    n --> n'
                    let rest = filter (/= t) ds
                    go rest
                Nothing -> do
                    case find (\((_, d1), (_,d2)) -> isJust $ resolve d1 d2) cp of
                        Nothing -> return ()
                        Just ((n1, d1), (n2, d2)) -> do
                            let d3 = fromJust $ resolve d1 d2
                            n3 <- disjunctNode d3
                            n1 --> n3
                            n2 --> n3
                            let rest = (n3, d3) : ds -- (filter (/= t1) $ filter (/= t2) $ ds)
                            go rest
      where
        empty (_, Disjunct []) = True
        empty _ = False
        cp :: [((NodeId, Disjunction), (NodeId, Disjunction))]
        cp = pairs ds

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


pairs :: [a] -> [(a,a)]
pairs [] = []
pairs as = go as $ tail as
  where
    go [] [] = []
    go _  [] = []
    go [] _  = []
    go (a:as) bss@(_:bs) = map (\b -> (a, b)) bss ++ go as bs

crossproduct :: [a] -> [b] -> [(a,b)]
crossproduct [] [] = []
crossproduct [] _  = []
crossproduct _  [] = []
crossproduct (a:as) bs = map (\b -> (a,b)) bs ++ crossproduct as bs


