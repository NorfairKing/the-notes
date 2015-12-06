module Functions.Application.Macro where

import           Types

import           Macro.Math
import           Macro.Text

-- * Function application
funapp :: Note -> Note -> Note
funapp n m = n <> negspace <> pars m
  where
    negspace :: Note
    negspace = commS "kern" <> raw "-2pt"

-- |
-- > fn = funapp
fn :: Note -> Note -> Note
fn = funapp

-- * Function application with two arguments
funapp2 :: Note -> Note -> Note -> Note
funapp2 f a b = funapp f $ cs [a, b]

-- |
-- > fn2 = funapp2
fn2 :: Note -> Note -> Note -> Note
fn2 = funapp2

-- * Member wise function application
mwfunapp :: Note -> Note -> Note
mwfunapp m n = m <> commS "," <> comm0 "square" <> commS "," <> n

-- |
-- > mwfn = mwfunapp
mwfn :: Note -> Note -> Note
mwfn = mwfunapp

-- |
-- > C-k OS
--
-- > (□) = mwfn
(□) :: Note -> Note -> Note
(□) = mwfn

