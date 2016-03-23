module FormalMethods.Macro where

import           Types

import           Macro.Arrows
import           Macro.MetaMacro
import           Macro.Tuple

import           Functions.Application.Macro

-- | Concrete signature
sig_ :: Note
sig_ = comm0 "Sigma"

-- | Concrete set of variables
vars_ :: Note
vars_ = mathcal "X"

-- | Term algebra
ta :: Note -> Note -> Note
ta s = fn $ mathcal "T" !: s

-- | Concrete defineTerm algebra
ta_ :: Note
ta_ = ta sig_ vars_

-- | Concrete set of equations
eqs_ :: Note
eqs_ = "E"

-- | Equational theory
et :: Note -> Note -> Note
et = tuple

-- | Concrete equational theory
et_ :: Note
et_ = et sig_ eqs_

-- | Right-oriented equations of a given set of equations
res :: Note -> Note
res = comm2 "overset" rightarrow

-- | Right-oriented equations of a given set of equations
les :: Note -> Note
les = comm2 "overset" leftarrow
