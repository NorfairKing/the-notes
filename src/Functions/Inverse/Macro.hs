module Functions.Inverse.Macro where

import           Types

import qualified Relations.Basics.Macro as R (inv)

-- | Inverse of a given function
inv :: Note -> Note
inv = R.inv

