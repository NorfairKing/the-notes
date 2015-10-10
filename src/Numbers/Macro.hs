module Numbers.Macro where

import           Sets.Macro
import           Types

natural :: Note -> Note
natural n = n ∈ naturals

realsp :: Note
realsp = reals ^: "+"

realsn :: Note
realsn = reals ^: "n"
