module Logic.PropositionalLogic.TruthTables where

import           Prelude

import           Data.List                         (nub, sortBy)
import           Data.Ord                          (comparing)

import           Logic.PropositionalLogic.Macro
import           Logic.PropositionalLogic.Sentence
import           Notes                             hiding (not, or)
import qualified Notes                             as N


renderLiteral :: Literal -> Note
renderLiteral (Lit True)           = true
renderLiteral (Lit False)          = false
renderLiteral (Symbol s)           = raw s

renderSentence :: Sentence -> Note
renderSentence (Literal l)          = renderLiteral l
renderSentence (Not (Literal l))    = N.not $ renderLiteral l
renderSentence (Not s@(Not _))      = N.not $ renderSentence s
renderSentence (Not s)              = pars $ N.not $ renderSentence s
renderSentence (Or s1 s2)           = pars $ renderSentence s1 ∨ renderSentence s2
renderSentence (And s1 s2)          = pars $ renderSentence s1 ∧ renderSentence s2
renderSentence (Implies s1 s2)      = pars $ renderSentence s1 ⇒ renderSentence s2
renderSentence (Equiv s1 s2)        = pars $ renderSentence s1 ⇔ renderSentence s2

renderCNFSentence :: Sentence -> Note
renderCNFSentence s = if isCNF s
                        then go s
                        else renderSentence s
  where
    go (Or s1 s2)           = go s1 ∨ go s2
    go (And s1 s2)          = (go s1 <> quad) ∧ (quad <> go s2)
    go s = renderSentence s


truthTableOf :: Sentence -> Note
truthTableOf s = truthTableOfExprs [s]

truthTableOfExprs :: [Sentence] -> Note
truthTableOfExprs exs = linedTable header content
  where
    exprs = sortBy (comparing sentenceDepth) $ nub $ concatMap infixSubs exs
    symbols = nub $ concatMap symbolsOf exprs
    states = possibleStates symbols
    header :: [Note]
    header = map renderSentence exprs
    content :: [[Note]]
    content = map row states
    row :: [(Text, Bool)] -> [Note]
    row vals = map (\e -> raw $ render $ evaluate $ fillInWith vals e) exprs

renderTransformation :: Sentence -> Note
renderTransformation = align_ . map (\(s, e) -> renderCNFSentence s & text (raw $ " " <> e)) . cnfTransformation


