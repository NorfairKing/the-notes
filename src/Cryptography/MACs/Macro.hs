module Cryptography.MACs.Macro where

import           Types

import           Functions.Application.Macro

-- * MAC

-- | Tag space
tsp_ :: Note
tsp_ = mathcal "T"

-- | Concrete MAC function
mfn_ :: Note
mfn_ = "f"

-- | Computation of tag of message and key
mfn :: Note -> Note -> Note
mfn = fn2 mfn_
