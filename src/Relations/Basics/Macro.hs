module Relations.Basics.Macro where

import           Types

import           Macro.MetaMacro

-- * Relation

-- | Standard relation symbol
rel_ :: Note
rel_ = "R"

-- | Element of given relation
elem :: Note -- ^ Relation
      -> Note -> Note -> Note
elem r v w = v <> commS "," <> r <> commS "," <> w

-- | Element of @rel_@
elem_ :: Note -> Note -> Note
elem_ = elem rel_

-- * Inverse relation

-- | Inverse of a given relation
inv :: Note -> Note
inv n = n ^: (-1)

-- * Unit relation

-- | The n-th order unit relation
unit :: Note -> Note
unit n = unit_ !: n

-- | The generic unit relation
unit_ :: Note
unit_ = "I"
