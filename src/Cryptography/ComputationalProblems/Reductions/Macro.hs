module Cryptography.ComputationalProblems.Reductions.Macro where

import           Types

import           Functions.Application.Macro

-- | Concrete reduction function
red_ :: Note
red_ = rho

-- | Apply concrete reduction function
red :: Note -> Note
red = fn red_
