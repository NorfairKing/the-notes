module Logic.TemporalLogic.Macro where

import           Types

import           Macro.MetaMacro
import           Macro.Text

import           Logic.AbstractLogic.Macro

-- | The 'next' temporal logic operator
next :: Note -> Note
next = mappend $ comm0 "bigcirc"

-- | The 'until' temporal logic operator
until :: Note -> Note -> Note
until = binop $ commS "," <> mathcal "U" <> commS ","

-- | Infix version of the 'until' temporal logic operator
(.∪) :: Note -> Note -> Note
(.∪) = until

-- | Eventually
evnt :: Note -> Note
evnt = mappend $ comm0 "Diamond"

-- | Always
alws :: Note -> Note
alws = mappend $ comm0 "Box"

-- | Satisfies
satis :: Note -- Word
          -> Note -- Position
          -> Note -- Formula
          -> Note
satis w p = lent $ cs [w, p]

-- | Language of a formula
languageOf :: Note -- Formula
           -> Note
languageOf = (!:) "L"
