module Functions.Application where

import           Notes

import           Sets.Basics                 (subset)

import           Functions.Basics            (function)

import           Functions.Application.Macro
import           Functions.Basics.Macro

makeDefs [
      "member-wise application"
    ]

application :: Note
application = note "application" $ do
    memberwiseApplication

memberwiseApplication :: Note
memberwiseApplication = de $ do
    s ["Let ", m funfunc_, " be a ", function]
    s [the, memberWiseApplication', " of ", m funfunc_, " to a ", subset, " ", m ss, " of ", m dom_, " is the set of all applications of ", m fun_, " to members of ", m ss, " and is denoted as ", m (fun_ `mwfn` ss)]
    ma $ fun_ `mwfn` ss === setcmpr (fun_ `fn` e) (e ∈ ss)
  where
    ss = "S"
    e = "s"
