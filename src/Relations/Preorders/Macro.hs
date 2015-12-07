module Relations.Preorders.Macro where

import           Types

import           Macro.Math
import           Macro.Relations.Macro


-- * Preorder

-- | The standard set for preorders
preordset_ :: Note
preordset_  = "X"

-- | The standard preorder sign
preord_ :: Note
preord_ = commS "sqsubseteq" <> " "

-- | The standard reverse preorder sign
ipreord_ :: Note
ipreord_ = commS "sqsupseteq" <> " "

-- | A preordered set given a set and a preorder
relpreord :: Note -- ^ Set
          -> Note -- ^ Preorder
          -> Note
relpreord = tuple

-- | The preordered set of @preordset_@ with @preord_@
relpreord_ :: Note
relpreord_ = relpreord preordset_ preord_

-- | Application of a given preorder
inpreord :: Note -- ^ Preorder
         -> Note -> Note -> Note
inpreord = inrel_

-- | Application of @preord_@
inpreord_ :: Note -> Note -> Note
inpreord_ = inpreord preord_

