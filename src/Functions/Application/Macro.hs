module Functions.Application.Macro where

import           Types

import           Macro.Math
import           Macro.Text

-- * Function application
app :: Note -> Note -> Note
app n m = n <> negspace <> pars m
  where
    negspace :: Note
    negspace = commS "kern" <> raw "-2pt"

-- |
-- > fn = app
fn :: Note -> Note -> Note
fn = app

-- | Infix operator for function application
(-:) :: Note -> Note -> Note
(-:) = app

-- * Function application with two arguments
app2 :: Note -> Note -> Note -> Note
app2 f a b = app f $ cs [a, b]

-- |
-- > fn2 = app2
fn2 :: Note -> Note -> Note -> Note
fn2 = app2

-- * Function application with three arguments
app3 :: Note -> Note -> Note -> Note -> Note
app3 f a b c = app f $ cs [a, b, c]

-- |
-- > fn3 = app3
fn3 :: Note -> Note -> Note -> Note -> Note
fn3 = app3

-- * Member wise function application
mwapp :: Note -> Note -> Note
mwapp m n = m <> commS "," <> comm0 "square" <> commS "," <> n

-- |
-- > mwfn = mwfunapp
mwfn :: Note -> Note -> Note
mwfn = mwapp

-- |
-- > C-k OS
--
-- > (□) = mwfn
(□) :: Note -> Note -> Note
(□) = mwfn

