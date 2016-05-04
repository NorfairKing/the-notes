module Macro.Numbers.Macro where

import           Functions.Application.Macro
import           Macro.MetaMacro

import           Types

realsp :: Note
realsp = reals ^: "+"

realsn :: Note
realsn = reals ^: "n"

-- Complex conjugate
conj :: Note -> Note
conj = overline

-- | Euler's totient function
etot :: Note -> Note
etot = fn phi

