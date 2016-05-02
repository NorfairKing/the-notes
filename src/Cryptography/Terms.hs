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

    , "one-way function"
    , "function inversion game"

    , "digital signature scheme"
    , "DSS"
    , "signing key"
    , "signature verification key"
    , "signature"
    , "signature space"
    , "signing key space"
    , "verification key space"
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
