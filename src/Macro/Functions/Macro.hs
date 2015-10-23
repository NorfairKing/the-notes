module Macro.Functions.Macro where

import           Types

import           Macro.Math
import           Macro.Text

import           Macro.Sets.CarthesianProduct


-- Functions
fun :: Note -> Note -> Note -> Note
fun m n o = m <> ":" <> raw "\\ " <> n <> rightarrow <> o

func :: Note -> Note -> Note -> Note -> Note -> Note
func m n o p q = fun m n o <> ":" <> raw "\\ " <> p <> comm0 "mapsto" <> q

func2 :: Note -> Note -> Note -> Note -> Note -> Note -> Note -> Note
func2 m n1 n2 o p1 p2 q = func m (n1 ⨯ n2) o (tuple p1 p2) q

funinv :: Note -> Note
funinv n = n ^: (-1)

funapp :: Note -> Note -> Note
funapp n m = n <> pars m

funapp2 :: Note -> Note -> Note -> Note
funapp2 f a b = funapp f $ cs [a, b]

fn :: Note -> Note -> Note
fn = funapp

fn2 :: Note -> Note -> Note -> Note
fn2 = funapp2


-- Distance function symbol
fundist :: Note
fundist = "d"

-- Function metric
funm :: Note
funm = fundist

fdist_ :: Note -> Note -> Note -> Note
fdist_ = funapp2

fdist :: Note -> Note -> Note
fdist = fdist_ fundist


-- Norms
norm_ :: Note -> Note -> Note
norm_ n b = autoBrackets dblPipe dblPipe b !: n

-- Arccos
arccos_ :: Note -> Note
arccos_ = funapp arccos

