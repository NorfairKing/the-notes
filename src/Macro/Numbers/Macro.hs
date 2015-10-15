module Macro.Numbers.Macro where

import           Macro.Sets.Macro

import           Types

natural :: Note -> Note
natural n = n ∈ naturals

realsp :: Note
realsp = reals ^: "+"

realsn :: Note
realsn = reals ^: "n"
