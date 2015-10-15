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

fn :: Note -> Note -> Note
fn = funapp


-- Distance function symbol
fundist :: Note
fundist = "d"

-- Function metric
funm :: Note
funm = fundist

