module Geometry.AffineSpaces where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           LinearAlgebra.VectorSpaces.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Sets.Basics.Terms

import           Geometry.AffineSpaces.Macro
import           Geometry.AffineSpaces.Terms

affineSpaces :: Note
affineSpaces = section "Affine Spaces" $ do
    pointDefinition
    affineSpaceDefinition

    affineSetDefinition
    convexSetDefinition
    convexFunctionDefinition
    concaveFunctionDefinition
    strictlyConvexFunctionDefinition

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

affineSetDefinition :: Note
affineSetDefinition = de $ do
    lab affineSetDefinitionLabel
    let a = "A"
    s ["An ", affineSet', " ", m a, " is a set that contains the line through any two distinct points in the ", set]
    ma $ do
        let (x, y) = ("x", "y")
        fa (x ∈ a) $ fa (y ∈ a) $ fa (theta ∈ reals) $ x ≠ y ⇒ theta * x + (pars $ 1 - theta) * y ∈ a

convexSetDefinition :: Note
convexSetDefinition = de $ do
    lab convexSetDefinitionLabel
    let a = "A"
    s ["An ", convexSet', " ", m a, " is a set that contains the line segment through any two distinct points in the ", set]
    ma $ do
        let (x, y) = ("x", "y")
        fa (x ∈ a) $ fa (y ∈ a) $ fa (theta ∈ ccint 0 1) $ x ≠ y ⇒ theta * x + (pars $ 1 - theta) * y ∈ a

convexFunctionDefinition :: Note
convexFunctionDefinition = de $ do
    lab convexFunctionDefinitionLabel
    let f = fun_
        n = "n"
        rn = reals ^ n
    s ["A ", function, " ", m $ fun f rn reals, " is called a ", convexFunction', " if ", m $ dom f, " is a ", convexSet, " and the following property holds"]
    ma $ do
        let (x, y) = ("x", "y")
        fa (x ∈ rn) $ fa (y ∈ rn) $ fn f (theta * x + (pars $ 1 - theta) * y) <= theta * fn f x + (pars $ 1 - theta) * fn f y

    todo "Are we sure that this is the right place to put this definition?"

concaveFunctionDefinition :: Note
concaveFunctionDefinition = de $ do
    lab concaveFunctionDefinitionLabel
    s ["A ", function, " ", m fun_, " is called a ", concaveFunction', " if ", m $ - fun_, " is a ", convexFunction]


strictlyConvexFunctionDefinition :: Note
strictlyConvexFunctionDefinition = de $ do
    lab strictlyConvexFunctionDefinitionLabel
    let f = fun_
        n = "n"
        rn = reals ^ n
    s ["A ", function, " ", m $ fun f rn reals, " is called a ", strictlyConvexFunction', " if ", m $ dom f, " is a ", convexSet, " and the following property holds"]
    ma $ do
        let (x, y) = ("x", "y")
        fa (x ∈ rn) $ fa (y ∈ rn) $ fn f (theta * x + (pars $ 1 - theta) * y) < theta * fn f x + (pars $ 1 - theta) * fn f y

affineSubspaces :: Note
affineSubspaces = subsection "Affine subspaces" $ do
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
