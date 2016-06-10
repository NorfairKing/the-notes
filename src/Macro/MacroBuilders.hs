module Macro.MacroBuilders where

import           Types

import           Macro.Math
import           Macro.MetaMacro

buildList :: Note -> Note -> (Note, Note, Note, Note)
buildList x k = (x1, x2, xk, xs)
  where
    x1 = x !: 1
    x2 = x !: 2
    xk = x !: k
    xs = list x1 x2 xk

buildiList :: Note -> Note -> Note -> (Note, Note, Note, Note, Note)
buildiList x k i = (x1, x2, xk, xi, xs)
  where
    x1 = x !: 1
    x2 = x !: 2
    xk = x !: k
    xi = x !: i
    xs = list x1 x2 xk
