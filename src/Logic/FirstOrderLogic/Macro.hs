module Logic.FirstOrderLogic.Macro where

import           Types

import           Macro.Text

-- Quantifiers
existentialQuantifier :: Note
existentialQuantifier = comm0 "exists"

thereExistsSign :: Note
thereExistsSign = existentialQuantifier

te :: Note -> Note -> Note
te n m = thereExistsSign <> n <> ":" <> commS " " <> m

tes :: [Note] -> Note -> Note
tes ns = te $ cs ns

universalQuantifier :: Note
universalQuantifier = comm0 "forall"

forallSign :: Note
forallSign = universalQuantifier

fa :: Note -> Note -> Note
fa n m = forallSign <> n <> ":" <> commS " " <> m

fas :: [Note] -> Note -> Note
fas ns = fa $ cs ns

