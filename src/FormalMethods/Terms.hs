module FormalMethods.Terms where

import           Notes hiding (constant)

makeDefs
    [ "signature"
    , "arity"
    , "constant"
    , "variable"
    , "term algebra"
    , "term"
    , "equation"
    , "rule"
    , "equational theory"
    , "equational derivation"
    , "free term algebra"
    , "free equational theory"
    , "quotient term algebra"
    , "substitution"
    , "position"
    , "subterm"
    , "matches"
    , "matching substitution"
    , "applicable"
    , "application"
    , "unifiable"
    , "unifier"
    , "equality step"
    , "equality relation"
    , "equality proof"
    , "infinite computations"
    , "termination"
    , "terminating"
    , "confluence"
    ]

eequalityStep :: Note -> Note
eequalityStep e = m e <> "-" <> equalityStep

eequalityRelation :: Note -> Note
eequalityRelation e = m e <> "-" <> equalityRelation
