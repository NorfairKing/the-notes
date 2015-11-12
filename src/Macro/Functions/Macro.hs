module Macro.Functions.Macro (
    module Macro.Functions.Macro

  , module Macro.Functions.Inverse
  , module Macro.Functions.Application
  ) where

import           Types

import           Macro.Math
import           Macro.Text

import           Macro.Sets.CarthesianProduct

import           Macro.Functions.Application
import           Macro.Functions.Inverse


-- Functions
fun :: Note -> Note -> Note -> Note
fun m n o = m <> ":" <> raw "\\ " <> n <> rightarrow <> o

func :: Note -> Note -> Note -> Note -> Note -> Note
func m n o p q = fun m n o <> ":" <> raw "\\ " <> p <> comm0 "mapsto" <> q

func2 :: Note -> Note -> Note -> Note -> Note -> Note -> Note -> Note
func2 m n1 n2 o p1 p2 q = func m (n1 ⨯ n2) o (tuple p1 p2) q

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

