module Logic.PropositionalLogic.TruthTables where

import           Prelude

import qualified Data.Text                      as T

import           Logic.PropositionalLogic.Macro
import           Notes                          hiding (not, or)
import qualified Notes                          as N

data Sentence = Lit Bool
              | Symbol Text
              | Not Sentence
              | Or Sentence Sentence
              | And Sentence Sentence
              | Implies Sentence Sentence
              | Equiv Sentence Sentence
    deriving (Eq)

instance Show Sentence where
    show (Lit True)         = "T"
    show (Lit False)        = "F"
    show (Symbol s)         = T.unpack s
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

evaluate :: Sentence -> Bool
evaluate (Lit b)            = b
evaluate (Symbol _)         = error $ "Symbols can't be evaluated"
evaluate (Not s)            = not $ evaluate s
evaluate (And s1 s2)        = evaluate s1 && evaluate s2
evaluate (Or s1 s2)         = evaluate s1 || evaluate s2
evaluate (Implies s1 s2)    = not (evaluate s1) || evaluate s2
evaluate (Equiv s1 s2)      = evaluate s1 == evaluate s2

cnfTransform :: Sentence -> Sentence
cnfTransform = last . cnfTransformation

cnfTransformation :: Sentence -> [Sentence]
cnfTransformation s = s : go s
  where
    go s | hasEquivs s              = let s' = removeEquivs s       in s' : go s'
         | hasImplies s             = let s' = removeImplies s      in s' : go s'
         | hasNotNots s             = let s' = undoNotNots s        in s' : go s'
         | hasTopNots s             = let s' = slideDownTopNots s   in s' : go s'
         | hasUndistributedOrs s    = let s' = distributeOrs s      in s' : go s'
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
    onlyAnds (Lit _) = True
    onlyAnds (Symbol _) = True
    onlyAnds _ = False

    onlyOrs (Or s1 s2) = onlyOrs s1 && onlyOrs s2
    onlyOrs (Not s) = done s
    onlyOrs (Lit _) = True
    onlyOrs (Symbol _) = True
    onlyOrs _ = False

    done (Lit _) = True
    done (Symbol _) = True
    done _ = False


symbolsOf :: Sentence -> [Text]
symbolsOf (Symbol s) = [s]
symbolsOf s = concatMap symbolsOf $ subExprs s


renderSentence :: Sentence -> Note
renderSentence (Lit True)       = true
renderSentence (Lit False)      = false
renderSentence (Symbol s)       = raw s
renderSentence (Not s)          = N.not $ renderSentence s
renderSentence (Or s1 s2)       = renderSentence s1 ∨ renderSentence s2
renderSentence (And s1 s2)      = renderSentence s1 ∧ renderSentence s2
renderSentence (Implies s1 s2)  = renderSentence s1 ⇒ renderSentence s2
renderSentence (Equiv s1 s2)    = renderSentence s1 ⇔ renderSentence s2


fillInWith :: [(Text, Bool)] -> Sentence -> Sentence
fillInWith vs = mapSub go
  where
    go (Symbol s) = case lookup s vs of
                        Nothing -> Symbol s
                        Just b  -> Lit b
    go s = s


possibleStates :: [Text] -> [[(Text, Bool)]]
possibleStates [] = [[]]
possibleStates (s:ss) = [ t:r | t <- theseStates, r <- rest ]
  where
    theseStates = [(s, True), (s, False)]
    rest = possibleStates ss



truthTableOf :: Sentence -> Note
truthTableOf s = linedTable header content
  where
    exprs = infixSubs s
    states = possibleStates $ symbolsOf s
    header :: [Note]
    header = map renderSentence exprs
    content :: [[Note]]
    content = map row states
    row :: [(Text, Bool)] -> [Note]
    row vals = map (\e -> raw $ render $ evaluate $ fillInWith vals e) exprs


infixSubs :: Sentence -> [Sentence]
infixSubs ss@(Not s)        = ss : infixSubs s
infixSubs s | isBinary s    = ss1 ++ [s] ++ ss2
  where [ss1, ss2] = map infixSubs $ subExprs s
infixSubs s                 = [s]












