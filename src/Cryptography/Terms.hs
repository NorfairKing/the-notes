module Cryptography.Terms where

import           Notes

import           Cryptography.SymmetricCryptography.Terms

makeDefs
    [ "algorithm"

    , "trapdoor one-way permutation"
    , "TWOP"
    , "trapdoor generator"
    , "trapdoor function"
    , "trapdoor"

    , "RSA"

    , "digital signature scheme"
    , "DSS"
    , "signing key"
    , "verification key"
    , "signature verification key"
    , "signature"
    , "signature space"
    , "signing key space"
    , "verification key space"
    , "key-pair distribution"
    , "signing algorithm"
    , "signature verification algorithm"
    , "signature forgery game"
    , "one-time signature scheme"
    , "Lamport One-time signature scheme"

    , "full domain hash"
    , "FDH"

    , "hash function"
    , "hash"
    , "collision-finding game"
    , "collision resistant"
    ]

nMesg :: Note -> Note
nMesg n = m n <> "-" <> message
