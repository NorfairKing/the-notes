module Cryptography.KeyEncapsulation where

import           Notes

import           Functions.Basics.Macro
import           Probability.RandomVariable.Terms

import           Cryptography.PublicKeyEncryption.Macro
import           Cryptography.PublicKeyEncryption.Terms
import           Cryptography.SymmetricCryptography.Macro
import           Cryptography.SymmetricCryptography.Terms

import           Cryptography.KeyEncapsulation.Macro
import           Cryptography.KeyEncapsulation.Terms

keyEncapsulationS :: Note
keyEncapsulationS = section "Key encapsulation" $ do
    keyEncapsulationMechanismDefinition

keyEncapsulationMechanismDefinition :: Note
keyEncapsulationMechanismDefinition = de $ do
    s ["Let", m pksp_, "be a", publicKeySpace <> ",", m sksp_, "a", secretKeySpace <> ",", m ksp_, "a symmetric", keySpace, and, m csp_, "a", ciphertextSpace]
    s ["A", keyEncapsulationMechanism', or, kEM', m kem_, "consists of..."]
    let d = "D"
    itemize $ do
        item $ s [m d       <> ": a" , probabilityDistribution, "on", m $ pksp_ ⨯ sksp_, "called the", keyPairDistribution']
        item $ s [m encapf_ <> ": a randomized", encapsulationFunction', m $ fun encapf_ pksp_ $ csp_ ⨯ ksp_]
        item $ s [m decapf_ <> ": a", decapsulationFunction', m $ fun decapf_ (csp_ ⨯ ksp_) ksp_]
    let p_ = "p"
        s_ = "s"
        c_ = "c"
        k_ = "k"
    s ["... such that for every", publicKey, "/", secretKey, "pair", m $ tuple p_ s_, and, m $ tuple c_ k_ =: encap p_, "it holds that", m $ decap c_ s_ =: k_]

