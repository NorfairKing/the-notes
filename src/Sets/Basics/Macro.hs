module Sets.Basics.Macro where

import           Types

subseteqsign :: Note
subseteqsign = comm0 "subseteq"

subseteq :: Note -> Note -> Note
subseteq m n = m <> subseteqsign <> n
