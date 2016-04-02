{-# LANGUAGE QuasiQuotes #-}
module Cryptography.MACs where

import           Notes                                    hiding (cyclic,
                                                           inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Probability.ProbabilityMeasure.Terms

import           Cryptography.MACs.Macro
import           Cryptography.MACs.Terms
import           Cryptography.SymmetricCryptography.Macro
import           Cryptography.SymmetricCryptography.Terms

mACS :: Note
mACS = section "Message Authentication Codes" $ do
    messageAuthenticationCodeDefinition
    messageAuthenticationCodeSecurityDefinition

    subsection "Approaches to Authenticated Encryption" $ do
        encryptAndMACDefinition
        encryptThenMACDefinition
        mACThenEncryptDefinition

    encryptThenMacInsecureForSameKey
    unforgableMayLeakPlain
    todo "define the confidentiality property for MAC's"



messageAuthenticationCodeDefinition :: Note
messageAuthenticationCodeDefinition = de $ do
    lab messageAuthenticationCodeDefinitionLabel
    lab mACDefinitionLabel
    lab tagSpaceDefinitionLabel
    let f = "f"
    s ["A", messageAuthenticationCode', "(" <> mAC' <> ")", "for a message space", m msp_, ", " <> keySpace, m ksp_, and, tagSpace', m tsp_, "is a", function, m $ fun2 f msp_ ksp_ tsp_]

messageAuthenticationCodeSecurityDefinition :: Note
messageAuthenticationCodeSecurityDefinition = de $ do
    lab cMASecureDefinitionLabel
    let t = "t"
        f_ = "f"
        f = fn2 f_
    s ["A", m t <> "-message", mACForgery', "game", "for a", mAC, m f_, "between an", adversary, "and a", challenger, "is played as follows"]
    let k = "k"
    enumerate $ do
        item $ s [the, challenger, "chooses a secret key", m $ k ∈ ksp_, "uniformly at random"]
        let i = "i"
            mi = "m" !: i
        item $ s [the, adversary, "can choose up to", m t, messages, m mi, "and receive their", mAC <> "-values", m $ f mi k]
        let m' = "m'"
            z = "z"
        item $ do
            s [the, adversary, "chooses a", message, m m', "and a", mAC <> "-value", m z]
            s ["He wins the game if", m $ z =: f m' k, and, m m', "was not asked as a query in step 2"]

    s ["A", mAC, function, "is called", cMASecure', "if no feasible", adversary, "wins this game with a non-negligible", probability]

encryptThenMACDefinition :: Note
encryptThenMACDefinition = de $ do
    lab encryptThenMACDefinitionLabel
    s [the, encryptThenMAC', "(" <> etM' <> ")", "approach uses a", symmetricCryptosystem, m scs_, "with", messageSpace, m msp_ <> ",", keySpace, m ksp_, and, ciphertextSpace, m csp_, anda, mAC, m mfn_, "with", messageSpace, m csp_, and, keySpace, m ksp_, "as follows"]
    let mesg = "m"
        tag = "t"
        ciph = "c"
    s ["First the", plaintext, m mesg, "is encrypted to", m ciph <> ", then a", mAC, m tag, "is produced based on the resulting", ciphertext]
    s [the, "result is the tuple", m $ tuple ciph tag]
    tikzFig "Encrypt then MAC" [] $ raw $ [litFile|src/Cryptography/MACs/encryptThenMACTikZ.tex|]


encryptAndMACDefinition :: Note
encryptAndMACDefinition = do
    de $ do
        lab encryptAndMACDefinitionLabel
        s [the, encryptAndMAC', "(" <> eaM' <> ")", "approach uses a", symmetricCryptosystem, m scs_, "with", messageSpace, m msp_ <> ",", keySpace, m ksp_, and, ciphertextSpace, m csp_, anda, mAC, m mfn_, "with", messageSpace, m msp_, and, keySpace, m ksp_, "as follows"]
        let mesg = "m"
            tag = "t"
            ciph = "c"
        s ["First the", plaintext, m mesg, "is encrypted to", m ciph]
        s ["A", mAC, m tag, "is produced based on the original", plaintext]
        s [the, "result is the tuple", m $ tuple mesg tag]
        tikzFig "Encrypt then MAC" [] $ raw $ [litFile|src/Cryptography/MACs/encryptAndMACTikZ.tex|]
    nte $ do
        s ["Note that this approach could equivalently be defined with two different", keySpaces]
        s ["The equivalence is then in modeling both of them as part of a tuple and having the", symmetricCryptosystem, and, mAC, "each use its own part of a tuple"]

mACThenEncryptDefinition :: Note
mACThenEncryptDefinition = de $ do
    lab mACThenEncryptDefinitionLabel
    s [the, mACThenEncrypt', "(" <> mtE' <> ")", "approach uses a", mAC, m mfn_, with, messageSpace, m msp_ <> ",", keySpace, m ksp_, and, tagSpace, m tsp_, anda, symmetricCryptosystem, m scs_, with, messageSpace, m (msp_ ⨯ tsp_) <> ",", keySpace, m ksp_, and, ciphertextSpace, m csp_, "as follows"]
    let mesg = "m"
        tag = "t"
        ciph = "c"
    s ["First the", plaintext, m mesg, "is tagged with the", mAC, m tag, ", then the tuple", m $ tuple mesg tag, "is encrypted to", m ciph]
    s [the, "result is", m ciph]
    tikzFig "Encrypt then MAC" [] $ raw $ [litFile|src/Cryptography/MACs/mACThenEncryptTikZ.tex|]


encryptThenMacInsecureForSameKey :: Note
encryptThenMacInsecureForSameKey = thm $ do
    s ["Let", m mfn_, "be a", mAC, "that is", cMASecure]
    let mesg = "m"
        k = "k"
    s ["If a single", message, m mesg, "is encrypted with the", oneTimePad, "and the result is tagged by this", mAC, "with the same", key, m k, "the resulting scheme, called", encryptThenMAC', "with the same key, the result is no longer", cMASecure, "if an", adversary, "has an encryption oracle"]
    todo "define encrypt then MAC separately"

    proof $ do
        s ["The following", adversary, "can win the", mACForgery, "game with", probability, m 1]
        itemize $ do
            let c = "c"
            item $ s [the, adversary, "chooses a random", message, m mesg, "and receives its encryption", m c, "from the encryption oracle"]
            item $ s [the, adversary, "wins the", mACForgery, "game by submitting", m $ mfn c k]


unforgableMayLeakPlain :: Note
unforgableMayLeakPlain = thm $ do
    s ["There exists a", mAC, "that is", cMASecure, "but will leak the entire", plaintext]
    todo "define encrypt and MAC separately"
    proof $ do
        s ["Let", m mfn_, "be a", mAC, "that is", cMASecure]
        s [the, mAC, m $ mfn_ <> "'", "that appends the", plaintext, "to the tag of", m mfn_, "is still", cMASecure, "but leaks the", plaintext]
