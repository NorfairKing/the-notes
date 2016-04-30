module Cryptography.KeyEncapsulation where

import           Notes

import           Functions.Basics.Macro
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
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
    keyEncapsulationINDCCAGameDefinition



keyEncapsulationMechanismDefinition :: Note
keyEncapsulationMechanismDefinition = do
    de $ do
        s ["Let", m pksp_, "be a", publicKeySpace <> ",", m sksp_, "a", secretKeySpace <> ",", m ksp_, "a symmetric", keySpace, and, m csp_, "a", ciphertextSpace]
        s ["A", keyEncapsulationMechanism', or, kEM', m kem_, "consists of..."]
        itemize $ do
            item $ s [m kpdist_ <> ": a" , probabilityDistribution, "on", m $ pksp_ ⨯ sksp_, "called the", keyPairDistribution']
            item $ s [m encapf_ <> ": a randomized", encapsulationFunction', m $ fun encapf_ pksp_ $ csp_ ⨯ ksp_]
            item $ s [m decapf_ <> ": a", decapsulationFunction', m $ fun decapf_ (csp_ ⨯ ksp_) ksp_]
        let p_ = "p"
            s_ = "s"
            c_ = "c"
            k_ = "k"
        s ["... such that for every", publicKey, "/", secretKey, "pair, sampled from", m kpdist_ <> ",", m $ tuple p_ s_, and, m $ tuple c_ k_ =: encap p_, "it holds that", m $ decap c_ s_ =: k_]
    nte $ do
        s ["Note that this equality does not have to hald for every", publicKey, "/", secretKey, "pair"]
        s ["Indeed, most", kEMs, "will have a", keyPairDistribution, "in which some", keyPairs, "have", probability, "mass", m 0]

keyEncapsulationINDCCAGameDefinition :: Note
keyEncapsulationINDCCAGameDefinition = de $ do
    s ["Let", m pksp_, "be a", publicKeySpace <> ",", m sksp_, "a", secretKeySpace <> ",", m ksp_, "a symmetric", keySpace, and, m csp_, "a", ciphertextSpace]
    s [the, iNDCCA, "game for a", keyEncapsulationMechanism, m kem_, "proceeds as follows"]
    let p_ = "p"
        s_ = "s"
        c_ = "c"
        k_ = "k"
        b = "b"
        b' = b <> "'"
        r = "r"
    enumerate $ do
        item $ do
            s [the, challenger, "samples a", keyPair, m $ (tuple p_ s_) ∈ (pksp_ ⨯ sksp_), "of a", publicKey, anda, secretKey, "according to the", keyPairDistribution, m kpdist_, "and computes a", ciphertext, "/", symmetricKey, "pair", m $ tuple c_ k_ =: encap p_]
            s ["He then samples a uniform bit", m b, "and sends", m $ triple p_ c_ k_, "to the adversary if", m b, "is not set and otherwise", m $ triple p_ c_ r, "for an independently and uniformly sampled", m $ r ∈ ksp_, "if", m b, "is set"]
        let c_' = c_ <> "'"
            k_' = k_ <> "'"
        item $ s [the, adversary, "can choose", ciphertexts, m $ c_' ∈ csp_, "different from", m c_, "and receive their decapsulations", m $ k_' =: decap c_' s_, "from the", challenger]
        item $ s [the, adversary, "guesses", m b, "by outputting a bit", m b']
    s [the, adversary, "wins the game if he guesses", m b, "correctly and his", advantage, "is defined as follows"]
    ma $ 2 * (pars $ prob (b' =: b) - 1 /: 2)
