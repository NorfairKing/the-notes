module Cryptography.KeyAgreement where

import           Notes

import           Cryptography.SymmetricCryptography.Terms

-- import Cryptography.KeyAgreement.Macro
import           Cryptography.KeyAgreement.Terms

keyAgreementS :: Note
keyAgreementS = section "Key agreement" $ do
    diffieHellmanProtocolDefinition
    diffieHellmanManInTheMiddleAttack

diffieHellmanProtocolDefinition :: Note
diffieHellmanProtocolDefinition = de $ do
    lab diffieHellmanDefinitionLabel
    lab dHDefinitionLabel
    let a = "Alice"
        b = "Bob"
    s [the, "famous", diffieHellman', cryptographicProtocol, "for two parties", m a, and, m b, "goes as follows"]
    enumerate $ do
        let p = "p"
            g = "g"
        item $ s [m a, and, m b, "publicly agree on a prime", m p, "and a basis", m g]
        let x = "x"
            xa = x !: a
            xb = x !: b
            y = "y"
            ya = y !: a
            yb = y !: b
        item $ s [m a, "selects an exponent", m xa, "at random and computes", m $ ya =: g ^ (xa) `mod` p]
        item $ do
            s [m b, "selects an exponent", m xb, "at random and computes", m $ yb =: g ^ (xb) `mod` p]
            s [m ya, and, m yb, "are called the", halfkeys', "of the", diffieHellman, protocol]
        item $ s [m a, and, m b, "send their respective", halfkeys, "to eachother", "over an authenticated but otherwise insecure channel"]
        let kab = "K" !: (a <> b)
        item $ s [m a, "computes", m $ kab =: yb ^ xa]
        let kba = "K" !: (b <> a)
        item $ do
            s [m b, "computes", m $ kba =: ya ^ xb]
            s ["Because", m kab, "equals", m kba, ", " <> m a, and, m b, "now both have the same shared secret value"]
        ma $ kab =: yb ^ xa =: (g ^ xb) ^ xa =: (g ^ xa) ^ xb =: ya ^ xb =: kba

    todo "generalisation to arbitrary cyclic groups"


diffieHellmanManInTheMiddleAttack :: Note
diffieHellmanManInTheMiddleAttack = nte $ do
    s ["If the insecure channel used in the", diffieHellman, protocol, "is not authenticated, this protocol can be attacked trivially"]

    s ["If an", attacker, "can intercept and replace", messages, "they can set themselves up as an intermediate node and read/change any message that passes them"]
    s ["They do this by intercepting both halfkeys and sending back their own", halfkey, "to both to complete the", protocol]

