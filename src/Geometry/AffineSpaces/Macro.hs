module Geometry.AffineSpaces.Macro where

import           Types

import           Macro.MetaMacro

import qualified Macro.LinearAlgebra.Macro as LA


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
