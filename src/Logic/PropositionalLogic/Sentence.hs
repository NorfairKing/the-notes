module Logic.PropositionalLogic.Sentence where

import           Prelude

import           Data.String (IsString (..))

import           Data.List   (nub)
import           Data.Text   (Text)
import qualified Data.Text   as T

data Literal = Lit Bool
             | Symbol Text
    deriving (Eq)

instance Show Literal where
    show (Lit True)         = "T"
    show (Lit False)        = "F"
    show (Symbol s)         = T.unpack s

data Sentence = Literal Literal
              | Not Sentence
              | Or Sentence Sentence
              | And Sentence Sentence
              | Implies Sentence Sentence
              | Equiv Sentence Sentence
    deriving (Eq)

instance IsString Sentence where
    fromString = Literal . Symbol . T.pack

instance Show Sentence where
    show (Literal s)        = show s
    show (Not s)            = "¬" ++ show s
    show (Or s1 s2)         = "(" ++ show s1 ++ " ∨ " ++ show s2 ++ ")"
    show (And s1 s2)        = "(" ++ show s1 ++ " ∧ " ++ show s2 ++ ")"
    show (Implies s1 s2)    = "(" ++ show s1 ++ " ⇒ " ++ show s2 ++ ")"
    show (Equiv s1 s2)      = "(" ++ show s1 ++ " ⇔ " ++ show s2 ++ ")"

isBinary :: Sentence -> Bool
isBinary (Or _ _)       = True
isBinary (And _ _)      = True
isBinary (Implies _ _)  = True
isBinary (Equiv _ _)    = True
isBinary _              = False

subExprs :: Sentence -> [Sentence]
subExprs (Not s)            = [s]
subExprs (Or s1 s2)         = [s1, s2]
subExprs (And s1 s2)        = [s1, s2]
subExprs (Implies s1 s2)    = [s1, s2]
subExprs (Equiv s1 s2)      = [s1, s2]
subExprs _ = []

sentenceDepth :: Sentence -> Int
sentenceDepth s = 1 + (safeMax . map sentenceDepth . subExprs $ s)
  where
    safeMax [] = 0
    safeMax ms = maximum ms

mapSubs :: (Sentence -> Sentence) -> Sentence -> Sentence
mapSubs f (Not s)            = Not $ f s
mapSubs f (Or s1 s2)         = Or       (f s1) (f s2)
mapSubs f (And s1 s2)        = And      (f s1) (f s2)
mapSubs f (Implies s1 s2)    = Implies  (f s1) (f s2)
mapSubs f (Equiv s1 s2)      = Equiv    (f s1) (f s2)
mapSubs _ s                  = s

mapSub :: (Sentence -> Sentence) -> Sentence -> Sentence
mapSub f = f . mapSubs (mapSub f)

mapSub' :: (Sentence -> Sentence) -> Sentence -> Sentence
mapSub' f = mapSubs (mapSub' f) . f

mapHas :: (Sentence -> Bool) -> Sentence -> Bool
mapHas f s = f s || (any (mapHas f) $ subExprs s)

evalLit :: Literal -> Bool
evalLit (Lit b)     = b
evalLit (Symbol _)  = error $ "Symbols can't be evaluated"

evaluate :: Sentence -> Bool
evaluate (Literal l)        = evalLit l
evaluate (Not s)            = not $ evaluate s
evaluate (And s1 s2)        = evaluate s1 && evaluate s2
evaluate (Or s1 s2)         = evaluate s1 || evaluate s2
evaluate (Implies s1 s2)    = not (evaluate s1) || evaluate s2
evaluate (Equiv s1 s2)      = evaluate s1 == evaluate s2

cnfTransform :: Sentence -> Sentence
cnfTransform = last . map fst . cnfTransformation

cnfTransformation :: Sentence -> [(Sentence, Text)]
cnfTransformation s = (s, "") : go s
  where
    go s | hasEquivs s              = let s' = removeEquivs s       in (s', "Remove biconditionals") : go s'
         | hasImplies s             = let s' = removeImplies s      in (s', "Remove conditionals") : go s'
         | hasNotNots s             = let s' = undoNotNots s        in (s', "Double negation") : go s'
         | hasTopNots s             = let s' = slideDownTopNots s   in (s', "De Morgan") : go s'
         | hasUndistributedOrs s    = let s' = distributeOrs s      in (s', "Distributive law") : go s'
         | otherwise                = []

hasEquivs :: Sentence -> Bool
hasEquivs = mapHas go
  where
    go (Equiv _ _) = True
    go _ = False

removeEquivs :: Sentence -> Sentence
removeEquivs = mapSub go
  where
    go (Equiv s1 s2) = And (Implies s1 s2) (Implies s2 s1)
    go s = s


hasImplies :: Sentence -> Bool
hasImplies = mapHas go
  where
    go (Implies _ _) = True
    go _ = False

removeImplies :: Sentence -> Sentence
removeImplies = mapSub go
  where
    go (Implies s1 s2) = Or (Not s1) s2
    go s = s

hasNotNots :: Sentence -> Bool
hasNotNots = mapHas go
  where
    go (Not (Not _)) = True
    go _ = False

undoNotNots :: Sentence -> Sentence
undoNotNots = mapSub go
  where
    go (Not (Not s)) = s
    go s = s

hasTopNots :: Sentence -> Bool
hasTopNots = mapHas go
  where
    go (Not s) = isBinary s
    go _ = False

deMorgan :: Sentence -> Sentence
deMorgan (And s1 s2)    = Not (Or (Not s1) (Not s2))
deMorgan (Or s1 s2)     = Not (And (Not s1) (Not s2))
deMorgan s              = s

slideDownTopNots :: Sentence -> Sentence
slideDownTopNots = mapSub go
  where
    go (Not s) | isBinary s = Not (deMorgan s)
    go s = s

hasUndistributedOrs :: Sentence -> Bool
hasUndistributedOrs = mapHas go
  where
    go (Or (And _ _) _) = True
    go (Or _ (And _ _)) = True
    go _ = False

distributeOrs :: Sentence -> Sentence
distributeOrs = mapSub' go
  where
    go (Or (And s1 s2) s3) = And (Or s1 s3) (Or s2 s3)
    go (Or s1 (And s2 s3)) = And (Or s1 s2) (Or s1 s3)
    go s = s

isCNF :: Sentence -> Bool
isCNF = onlyAnds
  where
    onlyAnds (And s1 s2) = onlyAnds s1 && onlyAnds s2
    onlyAnds (Or s1 s2) = onlyOrs s1 && onlyOrs s2
    onlyAnds (Not s) = done s
    onlyAnds (Literal _) = True
    onlyAnds _ = False

    onlyOrs (Or s1 s2) = onlyOrs s1 && onlyOrs s2
    onlyOrs (Not s) = done s
    onlyOrs (Literal _) = True
    onlyOrs _ = False

    done (Literal _) = True
    done _ = False


symbolsOf :: Sentence -> [Text]
symbolsOf (Literal (Symbol s)) = [s]
symbolsOf s = nub $ concatMap symbolsOf $ subExprs s

fillInWith :: [(Text, Bool)] -> Sentence -> Sentence
fillInWith vs = mapSub go
  where
    go (Literal (Symbol s)) = case lookup s vs of
                                Nothing -> Literal (Symbol s)
                                Just b  -> Literal (Lit b)
    go s = s


possibleStates :: [Text] -> [[(Text, Bool)]]
possibleStates [] = [[]]
possibleStates (s:ss) = [ t:r | t <- theseStates, r <- rest ]
  where
    theseStates = [(s, True), (s, False)]
    rest = possibleStates ss


infixSubs :: Sentence -> [Sentence]
infixSubs ss@(Not s)        = ss : infixSubs s
infixSubs s | isBinary s    = ss1 ++ [s] ++ ss2
  where [ss1, ss2] = map infixSubs $ subExprs s
infixSubs s                 = [s]

