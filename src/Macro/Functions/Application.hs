module Macro.Functions.Application where

import           Types

import           Macro.Math
import           Macro.Text

funapp :: Note -> Note -> Note
funapp n m = n <> pars m

funapp2 :: Note -> Note -> Note -> Note
funapp2 f a b = funapp f $ cs [a, b]

fn :: Note -> Note -> Note
fn = funapp

fn2 :: Note -> Note -> Note -> Note
fn2 = funapp2

