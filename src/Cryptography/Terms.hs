module Cryptography.Terms where

import           Notes

makeDefs [
      "cryptographic scheme"
    , "cryptosystem"
    , "cryptographic protocol"
    , "protocol"
    , "party"
    , "agent"

    , "symmetric cryptosystem"

    , "message space"
    , "message"
    , "plaintext"
    , "ciphertext space"
    , "ciphertext"
    , "key space"
    , "key"
    , "randomness space"

    , "encryption function"
    , "decryption function"

    , "deterministic"
    , "cipher"

    , "adversary"
    , "challenger"
    , "attacker"
    , "advantage"

    , "indistinguishability chosen plaintext attack"
    , "IND-CPA"
    , "IND-CPA secure"

    , "non-adaptive IND-CPA"
    , "non-adaptively IND-CPA secure"

    , "indistinguishability chosen ciphertext attack"
    , "IND-CCA"
    , "IND-CCA secure"

    , "one-time pad"
    , "many-time pad"
    , "key-stream generator"
    , "additive stream cipher"

    , "pseudo-random generator"
    , "PRG"

    , "block cipher"
    , "block length"

    , "electronic codebook"
    , "ECB"

    , "cipher block chaining"
    , "initialisation vector"
    , "CBC"

    , "counter"
    , "CTR"

    , "message authentication code"
    , "MAC"
    , "tag space"

    , "MAC-forgery"
    , "CMA secure"

    , "Diffie-Hellman"
    , "DH"
    , "halfkey"

    , "discrete logarithm"
    , "DL"

    , "computational Diffie-Hellman"
    , "CDH"

    , "Diffie-Hellman triple"
    , "decisional Diffie-Hellman"
    , "DDH"

    , "public-key encryption scheme"
    , "PKE"
    , "key generator"
    , "key pair"
    , "public key"
    , "secret key"
    , "private key"
    , "ElGamal"

    , "trapdoor one-way permutation"
    , "TWOP"
    , "trapdoor generator"
    , "trapdoor"

    , "RSA"

    , "digital signature scheme"
    , "DSS"
    , "signing key"
    , "signature verification key"
    , "signature"
    , "signing algorithm"
    , "signature verification algorithm"
    , "signature forgery game"

    , "full domain hash"
    , "FDH"

    , "hash function"
    , "hash"
    , "collision-finding game"
    , "collision resistant"
    ]

makeThms
    [ "many time pad insecure"
    ]
