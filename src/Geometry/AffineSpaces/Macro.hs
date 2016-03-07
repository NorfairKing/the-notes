module Geometry.AffineSpaces.Macro where

import           Types

import           Functions.Application.Macro
import           Macro.MetaMacro

import qualified Macro.LinearAlgebra.Macro   as LA

-- | Projection onto a convex set
proj :: Note -> Note -> Note
proj a = fn $ "Proj" !: a

-- | Affine space with given dimension
aspace :: Note -> Note
aspace n = mathbb "A" ^: n

-- | Addition of point and vector
(<+>) :: Note -> Note -> Note
(<+>) = (LA.<+>)

-- | Substraction of two vectors

-- | Affine subspace given a point and a linear subspace
--
-- Mnemonic: (Directed) affine subspace
daspace :: Note -> Note -> Note
daspace = (<+>)
