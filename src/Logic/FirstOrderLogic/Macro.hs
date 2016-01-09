module Logic.FirstOrderLogic.Macro where

import           Types

import           Macro.Text

-- * Quantifiers

-- ** Existential quantifier
thereExistsSign :: Note
thereExistsSign = comm0 "exists"

te :: Note -> Note -> Note
te n m = thereExistsSign <> n <> ":" <> commS " " <> m

tes :: [Note] -> Note -> Note
tes ns = te $ cs ns

-- ** Universal quantifier
forallSign :: Note
forallSign = comm0 "forall"

fa :: Note -> Note -> Note
fa n m = forallSign <> n <> ":" <> commS " " <> m

fas :: [Note] -> Note -> Note
fas ns = fa $ cs ns

