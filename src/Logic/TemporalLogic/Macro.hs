module Logic.TemporalLogic.Macro where

import           Macro.MetaMacro
import           Types

-- | The 'next' temporal logic operator
next :: Note -> Note
next = mappend $ comm0 "textbigcircle"

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
