module LinearAlgebra.VectorSpaces (
      vectorSpaces

    , vectorSpaceDefinitionLabel
    ) where

import           Notes

import           Functions.Basics.Macro
import           Logic.FirstOrderLogic.Macro

vectorSpaces :: Note
vectorSpaces = note "vector-spaces" body

body :: Note
body = do
    section "Vector Spaces"
    vectorSpaceDefinition

vectorSpaceDefinitionLabel :: Label
vectorSpaceDefinitionLabel = Label Definition "vector-space"

vectorSpaceDefinition :: Note
vectorSpaceDefinition = de $ do
    lab vectorSpaceDefinitionLabel
    noindent
    enumerate $ do
        item $ do
            s ["Let ", m (fie_ lafield lafadd lafmul), " be a field and let ", m laset, " be a set"]
            refneeded "field"
            refneeded "set"
        item $ do
            s ["Let ", m (pars laadd), " be an internal binary operation on ", m laset]
            ma $ fun (pars laadd) (laset ⨯ laset) laset
            refneeded "binary operation"
        item $ do
            s ["Let ", m (pars lamul), " be a binary operation"]
            ma $ fun (pars lamul) (lafield ⨯ laset) laset
    s [m lavs, " is a ", term "vector space", over, m lafield, " if the following properties hold"]
    enumerate $ do
        item $ do
            s [m (grp_ laset laadd), " is a commutative group"]
            refneeded "commutative group"
        item $ do
            s [m (grp_ laset lamul), " is a monoid"]
            refneeded "monoid"
        item $ do
            s [m (pars laadd), is, distributive, wrt, m (pars $ lamul)]
        item $ do
            s [m (pars lamul), is, distributive, wrt, m (pars $ laadd)]
        item $ do
            "Mixed associativity:"
            ma $ fa (cs [rr, ss] ∈ lafield) $ (pars $ rr *. ss) <*> vv =: rr <*> (pars $ ss <*> vv)
  where
    rr = "r"
    ss = "s"
    vv = vec "v"

