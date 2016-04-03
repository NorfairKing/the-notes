module Cryptography.MACs.Terms where

import           Notes

makeDefs
    [ "message authentication code"
    , "MAC"
    , "tag space"
    , "tag"

    , "MAC-forgery"
    , "CMA secure"

    , "Encrypt-then-MAC"
    , "EtM"

    , "Encrypt-and-MAC"
    , "EaM"

    , "MAC-then-Encrypt"
    , "MtE"

    , "impersonation attack"
    , "substitution attack"

    , "uniform tags"
    , "independent tags"
    ]

makeThms
    [ "uniform tags impersonation probability bounded"
    , "independent tags substitution probability bounded"
    ]
