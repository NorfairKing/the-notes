module Macro.Numbers.Macro where

import           Types

import           Functions.Application.Macro
import           Macro.Math
import           Macro.MetaMacro
import           Macro.Sets.Macro


realsp :: Note
realsp = reals ^: "+"

realsn :: Note
realsn = reals ^: "n"

ereals :: Note
ereals = reals ∪ (setofs [minfty, pinfty])

erealsp :: Note
erealsp = realsp ∪ (setof pinfty)

erealsm :: Note
erealsm = realsn ∪ (setof pinfty)

-- Complex conjugate
conj :: Note -> Note
conj = overline

-- | Euler's totient function
etot :: Note -> Note
etot = fn phi

