module Cryptography.SymmetricCryptography.Terms where

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
    ]

makeThms
    [ "many time pad insecure"
    , "xor uniform"
    , "xor ECB insecure"
    ]
