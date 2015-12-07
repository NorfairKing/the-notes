module Relations.Equivalence.Macro where

import           Prelude                   (flip)
import           Types

import           Macro.Math
import           Macro.MetaMacro

import           Relations.Preorders.Macro

-- * Equivalence Relation

-- | Equivalence relation sing
eqrel_ :: Note
eqrel_ = comm0 "sim" <> raw "\\mkern-3mu"

-- | Application of arbitrary equivalence relation
ineqrel :: Note -> Note -> Note -> Note
ineqrel = inpreord

-- | Application of @eqrel_@
ineqrel_ :: Note -> Note -> Note
ineqrel_ = ineqrel eqrel_

-- | Infix operator for equivalence relation
(.~) :: Note -> Note -> Note
(.~) = ineqrel_

-- * Equivalence Classes

-- | The equivalence class of an element under a given equivalence relation
eqcl :: Note -- ^ Equivalence relation
     -> Note -- ^ Element
     -> Note
eqcl r x = sqbrac x !: r

-- | The equivalence class of an element under @eqrel_@
eqcl_ :: Note -> Note
eqcl_ = eqcl eqrel_

-- | The equivalence class of an element, equivalence relation omitted
eqc :: Note -> Note
eqc = sqbrac

-- * Quotient set

-- | The set of equivalence classes (Quotient set) of a given set under a given equivalence relation
eqcls :: Note -- ^ Equivalence relation
      -> Note -- ^ Set
      -> Note
eqcls r x = x <> "/" <> r

-- | The set of equivalence classes of a given set under @eqrel_@
eqcls_ :: Note -> Note
eqcls_ = eqcls eqrel_

-- |
-- > (./~) = flip eqcls
(./~) :: Note -> Note -> Note
(./~) = flip eqcls

