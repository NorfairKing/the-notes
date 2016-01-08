module Functions.Application where

import           Notes

import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Sets.Basics.Terms

import           Functions.Application.Macro
import           Functions.Application.Terms

application :: Note
application = note "application" $ do
    memberWiseApplicationDefinition

memberWiseApplicationDefinition :: Note
memberWiseApplicationDefinition = de $ do
    lab memberWiseApplicationDefinitionLabel
    s ["Let ", m funfunc_, " be a ", function]
    s [the, memberWiseApplication', " of ", m funfunc_, " to a ", subset, " ", m ss, " of ", m dom_, " is the set of all applications of ", m fun_, " to members of ", m ss, " and is denoted as ", m (fun_ `mwfn` ss)]
    ma $ fun_ `mwfn` ss === setcmpr (fun_ `fn` e) (e ∈ ss)
  where
    ss = "S"
    e = "s"
