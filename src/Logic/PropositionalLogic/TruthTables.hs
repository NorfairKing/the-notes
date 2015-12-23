module Logic.PropositionalLogic.TruthTables where

import           Prelude

import           Logic.PropositionalLogic.Macro
import           Logic.PropositionalLogic.Sentence
import           Notes                             hiding (not, or)
import qualified Notes                             as N


renderSentence :: Sentence -> Note
renderSentence (Lit True)           = true
renderSentence (Lit False)          = false
renderSentence (Symbol s)           = raw s
renderSentence (Not s@(Symbol _))   = N.not $ renderSentence s
renderSentence (Not s@(Not _))      = N.not $ renderSentence s
renderSentence (Not s)              = pars $ N.not $ renderSentence s
renderSentence s@(Or s1 s2)         = do
    let f = if isCNF s
            then id
            else pars
    f $ renderSentence s1 ∨ renderSentence s2
renderSentence s@(And s1 s2)        = do
    let f = if isCNF s
            then id
            else pars
    f $ renderSentence s1 ∧ renderSentence s2
renderSentence (Implies s1 s2)      = pars $ renderSentence s1 ⇒ renderSentence s2
renderSentence (Equiv s1 s2)        = pars $ renderSentence s1 ⇔ renderSentence s2


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

renderTransformation :: Sentence -> Note
renderTransformation = align_ . map (\(s, e) -> renderSentence s & text (raw $ " " <> e)) . cnfTransformation
