module Functions.Composition.Macro where

import           Types

import qualified Relations.Composite.Macro as R

-- * Relation Composition
comp :: Note -> Note -> Note
comp = R.comp

-- |
-- > C-k 0M
(●) :: Note -> Note -> Note
(●) = comp

