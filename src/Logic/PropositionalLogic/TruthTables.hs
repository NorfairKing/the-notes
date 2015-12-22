module Logic.PropositionalLogic.TruthTables where

import           Prelude

import           Notes   hiding (not, or)

data Sentence = Lit Bool
              | Symbol Text
              | Not Sentence
              | Or Sentence Sentence
              | And Sentence Sentence
              | Implies Sentence Sentence
              | Equiv Sentence Sentence
    deriving (Show, Eq)

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
mapSubs f s                  = s

mapSub :: (Sentence -> Sentence) -> Sentence -> Sentence
mapSub f = f . mapSubs (mapSub f)

mapSub' :: (Sentence -> Sentence) -> Sentence -> Sentence
mapSub' f = mapSubs (mapSub' f) . f

mapHas :: (Sentence -> Bool) -> Sentence -> Bool
mapHas f s = f s || (any (mapHas f) $ subExprs s)

evaluate :: Sentence -> Bool
evaluate (Lit b)            = b
evaluate (Symbol s)         = error $ "Symbols can't be evaluated"
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
    go (Not (Not s)) = True
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








