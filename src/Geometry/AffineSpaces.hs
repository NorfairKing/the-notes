module Geometry.AffineSpaces where

import           Notes

import           LinearAlgebra.VectorSpaces.Terms

import           Geometry.AffineSpaces.Macro
import           Geometry.AffineSpaces.Terms

affineSpaces :: Note
affineSpaces = note "affine-spaces" $ do
    section "Affine Spaces"
    pointDefinition
    affineSpaceDefinition

    affineSubspaces

pointDefinition :: Note
pointDefinition = de $ do
    lab pointDefinitionLabel
    let n = "n"
    s ["An ", m n, "-dimensional ", point', " is an ", m n, "-tuple"]

affineSpaceDefinition :: Note
affineSpaceDefinition = de $ do
    lab affineSpaceDefinitionLabel
    let n = "n"
    s ["An ", m n, "-dimensional ", affineSpace', " ", m $ aspace n, " is the set of all ", m n, "-dimensional ", point, "s"]

affineSubspaces :: Note
affineSubspaces = do
    subsection "Affine subspaces"
    affineSubspaceDefinition
    hyperplaneDefinition

affineSubspaceDefinition :: Note
affineSubspaceDefinition = de $ do
    lab affineSubspaceDefinitionLabel
    let (k, n, p) = ("k", "p", "n")
        aspace_ = aspace n
    s ["Let ", m p, " be a point in an ", affineSpace, " ", m aspace_, " and let ", m laset, " be a ", m k, "-dimensional ", linearSubspace_, " of ", m $ realVectorsSpace n]
    s [m $ daspace p laset, " is called the ", affineSubspace', " of ", m aspace_, " with ", direction', " ", m laset, " through ", m p]

hyperplaneDefinition :: Note
hyperplaneDefinition = de $ do
    lab hyperplaneDefinitionLabel
    let n = "n"
        aspace_ = aspace n
    s ["Let ", m aspace_, " be an ", m n, "-dimensional ", affineSpace]
    s ["Any ", m (pars $ n - 1), "-dimensional ", affineSubspace, " of ", m aspace_, " is called a ", hyperplane']
