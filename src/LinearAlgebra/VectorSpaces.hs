module LinearAlgebra.VectorSpaces where

import           Notes

import           Functions.Basics.Macro
import           Functions.BinaryOperation.Terms
import           Groups.Macro
import           Groups.Terms
import           Logic.FirstOrderLogic.Macro
import           Sets.Basics.Terms

import           LinearAlgebra.VectorSpaces.Terms

vectorSpaces :: Note
vectorSpaces = section "Vector Spaces" $ do
    vectorSpaceDefinition
    subsection "Linear Subspaces" $ do
        linearSubspaceDefinition
    subsection "Euclidean Vector Spaces" $ do
        euclideanVectorSpaceDefinition

    placeholder $ do
        lab matrixTimesTransposeIsSymmetricTheoremLabel
        lab inverseOfSymmetricMatrixIsSymmetricTheoremLabel


vectorSpaceDefinition :: Note
vectorSpaceDefinition = de $ do
    lab vectorSpaceDefinitionLabel
    lab vectorDefinitionLabel
    noindent
    enumerate $ do
        item $ do
            s ["Let ", m (fie_ lafield lafadd lafmul), " be a field and let ", m laset, " be a", set]
            refneeded "field"
        item $ do
            s ["Let", m (pars laadd), "be an internal", binaryOperation, "on", m laset]
            ma $ fun (pars laadd) (laset ⨯ laset) laset
        item $ do
            s ["Let ", m (pars lamul), "be a", binaryOperation]
            ma $ fun (pars lamul) (lafield ⨯ laset) laset
    s [m lavs, " is a ", term "vector space", over, m lafield, " if the following properties hold"]
    enumerate $ do
        item $ do
            s [m (grp laset laadd), " is a commutative group"]
            refneeded "commutative group"
        item $ do
            s [m (grp laset lamul), "is a", monoid]
        item $ do
            s [m (pars laadd), is, distributive, wrt, m (pars $ lamul)]
        item $ do
            s [m (pars lamul), is, distributive, wrt, m (pars $ laadd)]
        item $ do
            "Mixed associativity:"
            ma $ fa (cs [rr, ss] ∈ lafield) $ (pars $ rr *. ss) <*> vv =: rr <*> (pars $ ss <*> vv)
    s ["An element of ", m laset, " is called a ", vector']
    s ["In the context of a ", vectorSpace, " the neutral element of ", m $ pars laadd, " is call the ", origin']
  where
    rr = "r"
    ss = "s"
    vv = vec "v"

linearSubspaceDefinition :: Note
linearSubspaceDefinition = de $ do
    lab linearSubspaceDefinitionLabel
    let vs = lavs_ lafield laset laadd lamul
    s ["Let ", m vs, " be a ", vectorSpace]
    let w = "W"
    s ["A", vectorSpace, m $ lavs_ lafield w laadd lamul, " is called a ", linearSubspace', " of ", m vs, " if ", m w, " is a subset of ", m laset]


euclideanVectorSpaceDefinition :: Note
euclideanVectorSpaceDefinition = de $ do
    lab euclideanVectorSpaceDefinitionLabel
    lab euclideanVectorDefinitionLabel
    let p = "p"
    s ["A ", euclideanVectorSpace', " is a ", vectorSpace, " of the form ", m $ realVectorsSpace p, " with ", m $ natural p]
    s ["An element of ", m $ reals ^ p, " is called a ", euclideanVector']
