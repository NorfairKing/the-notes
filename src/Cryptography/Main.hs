{-# LANGUAGE QuasiQuotes #-}
module Cryptography.Main where

import           Notes                                hiding (inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Inverse.Terms
import           Logic.FirstOrderLogic.Macro
import           Probability.Independence.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Sets.Basics.Terms

import           Cryptography.Macro
import           Cryptography.Terms

cryptography :: Note
cryptography = chapter "Cryptography" $ do
    section "Symmetric cryptosystems" $ do
        cryptographicSchemeDefinition
        cryptographicProtocolDefinition
        symmetricCryptosystemDefinition
        deterministicCryptoSystem
        cipherDefinition

        oneTimePadDefinition
        additiveStreamCipherDefinition

        subsection "IND-CPA" $ do
            indcpaDefinition
            indcpaSecurityDefinition

        subsection "IND-CCA" $ do
            indccaDefinition
            indccaSecurityDefinition

        subsection "pseudorandomness" $ do
            pseudoRandomGeneratorDefinition

        subsection "block ciphers" $ do
            blockCipherDefinition

    section "Message Authentication Codes" $ do
        messageAuthenticationCodeDefinition
        messageAuthenticationCodeSecurityDefinition


cryptographicSchemeDefinition :: Note
cryptographicSchemeDefinition = de $ do
    lab cryptographicSchemeDefinitionLabel
    s ["A", cryptographicScheme', or, cryptosystem', "consists of several", functions]

cryptographicProtocolDefinition :: Note
cryptographicProtocolDefinition = de $ do
    lab cryptographicProtocolDefinitionLabel
    s ["A", cryptographicProtocol', "for a given", set, "of parties consists of, for each party, a precicely specified behavior in the interaction with the other parties"]

symmetricCryptosystemDefinition :: Note
symmetricCryptosystemDefinition = do
    de $ do
        lab symmetricCryptosystemDefinitionLabel
        lab messageSpaceDefinitionLabel
        lab ciphertextSpaceDefinitionLabel
        lab keySpaceDefinitionLabel
        s ["A", symmetricCryptosystem', "for a", messageSpace', m msp_, ", ", ciphertextSpace', m csp_, ", ", keySpace', m ksp_, and, randomnessSpace, m rsp_, "is a pair of", functions, m $ tuple enc_ dec_, "as follows"]
        itemize $ do
            item $ do
                s [m enc_, "is called an", encryptionFunction', "and must be a", total, function]
                ma $ fun3 enc_ msp_ ksp_ rsp_ csp_
            item $ do
                s [m dec_, "is called a", decryptionFunction', "and it is usually strictly a", partialFunction]
                ma $ fun2 dec_ csp_ ksp_ msp_
        let k = "k"
            m = "m"
            r = "r"
        ma $ fa (k ∈ ksp_)
           $ fa (m ∈ msp_)
           $ fa (r ∈ rsp_)
           $ dec (enc m k r) k =: m
    nte $ do
        s ["Practicality dictates that", m enc_, and, m dec_, "must be efficiently computable"]
        s ["This is called the practicality condition"]

deterministicCryptoSystem :: Note
deterministicCryptoSystem = de $ do
    s ["A", deterministic', cryptosystem, "is a system in which the", randomnessSpace, "is entirely ignored"]
    s ["We then model the", encryptionFunction, "as taking only two arguments and leave out the", randomnessSpace]

cipherDefinition :: Note
cipherDefinition = de $ do
    lab cipherDefinitionLabel
    s ["A", cipher', "is a", deterministic, symmetricCryptosystem]

oneTimePadDefinition :: Note
oneTimePadDefinition = de $ do
    lab oneTimePadDefinitionLabel
    s [the, oneTimePad', "is a", cipher, "with the following", encryptionFunction, and, decryptionFunction]
    let mesg = "m"
        k = "k"
    ma $ enc' mesg k =: mesg ⊕ k
    let c = "c"
    ma $ dec c k =: c ⊕ k

    tikzFig "One-Time Pad" [] $ raw $ [litFile|src/Cryptography/OTPTikZ.tex|]

    toprove_ "prove that this is in fact a cipher, that the functions invert each other."


oneTimePadSecure :: Note
oneTimePadSecure = prop $ do
    let n = "n"
    s [the, oneTimePad <> "'s", ciphertexts, "are", independent, "of their", messages, "for a given message length", m n]
    toprove_ "page 17 of crypto"

additiveStreamCipherDefinition :: Note
additiveStreamCipherDefinition = de $ do
    let f_ = "f"
        f = fn f_
    s ["Let ", m f_, "be a", keyStreamGenerator]
    todo "define keystreamgenerator"
    s [the, additiveStreamCipher, "is a", cipher, "with the following", encryptionFunction, and, decryptionFunction]

    let mesg = "m"
        k = "k"
    ma $ enc' mesg k =: mesg ⊕ (f k)
    let c = "c"
    ma $ dec c k =: c ⊕ (f k)

    tikzFig "Additive Key-Stream Generator" [] $ raw $ [litFile|src/Cryptography/AKSGTikZ.tex|]

    toprove_ "prove that this is in fact a cipher, that the functions invert each other."

indcpaDefinition :: Note
indcpaDefinition = de $ do
    lab iNDCPADefinitionLabel
    lab indistinguishabilityChosenPlaintextAttackDefinitionLabel
    let t = "t"
        k = "k"
        i = "i"
    let b = "b"
        mb = "m" !: b
        c = "c"
    let b' = b <> "'"
    s ["A", m t <> "-message", indistinguishabilityChosenPlaintextAttack', "game", "(" <> iNDCPA' <> ")", "between a", challenger, "and an", adversary, "goes as follows"]
    enumerate $ do
        item $ s ["The challenger chooses a secret key", m k, "uniformly at random"]
        let mi = "m" !: i
            r = "r"
            ri = r !: i
        item $ s ["The adversary can choose up to", m t, "messages", m mi, "and receive their encryptions", m $ enc mi k ri, "for fresh and independent randomness values", m $ ri ∈ rsp_]
        let m0 = "m" !: 0
            m1 = "m" !: 1
        item $ s ["The adversary chooses two messages", m m0, and, m m1, "of the same length"]
        item $ s ["The challenger chooses a uniformly random bit", m b <> ", computes the encryption of ", m $ c =: enc mb k r, "for a fresh and independent randomness value", m $ r ∈ rsp_, "and returns it to the adversary"]
        item $ s ["The adversary can again choose up to", m t, "messages as in step 2, but the total number is limited by", m t]
        item $ s ["The adversary issues his guess", m b', "for", m b]
    s [the, advantage', "of the adversary in this game is defined as", m $ 2 * prob (b' =: b) - 1 /: 2]

indcpaSecurityDefinition :: Note
indcpaSecurityDefinition = de $ do
    lab iNDCPASecureDefinitionLabel
    let t = "t"
    s ["A", symmetricCryptosystem, "is called", iNDCPASecure', "if no feasible", adversary, "has a non-negligible", advantage, "in a", m t <> "-message", indistinguishabilityChosenPlaintextAttack, "game", "where", m t, "is only bounded by the adversary's running time"]

indccaDefinition :: Note
indccaDefinition = de $ do
    lab iNDCCADefinitionLabel
    lab indistinguishabilityChosenCiphertextAttackDefinitionLabel
    let t = "t"
        k = "k"
        i = "i"
    let b = "b"
        mb = "m" !: b
        c = "c"
    let b' = b <> "'"
    s ["A", m t <> "-message", indistinguishabilityChosenPlaintextAttack', "game", "(" <> iNDCCA' <> ")", "between a", challenger, "and an", adversary, "goes as follows"]
    enumerate $ do
        item $ s ["The challenger chooses a secret key", m k, "uniformly at random"]
        let mi = "m" !: i
            ci = "c" !: i
            r = "r"
            ri = r !: i
        item $ s ["The adversary can choose up to", m t, messages, m mi, or, ciphertexts, m ci, "and receive their encryptions", m $ enc mi k ri, "for fresh and independent randomness values", m $ ri ∈ rsp_, or, ciphertexts, "(in the case of", messages <> ") or receive their decryptions", m $ dec ci k, "(in the case of", ciphertexts <> ")"]
        let m0 = "m" !: 0
            m1 = "m" !: 1
        item $ s ["The adversary chooses two messages", m m0, and, m m1, "of the same length"]
        item $ s ["The challenger chooses a uniformly random bit", m b <> ", computes the encryption of ", m $ c =: enc mb k r, "for a fresh and independent randomness value", m $ r ∈ rsp_, "and returns it to the adversary"]
        item $ s ["The adversary can again choose up to", m t, messages, or, ciphertexts, "as in step 2, but the total number is limited by", m t]
        item $ s ["The adversary issues his guess", m b', "for", m b]
    s [the, advantage', "of the adversary in this game is defined as", m $ 2 * prob (b' =: b) - 1 /: 2]

indccaSecurityDefinition :: Note
indccaSecurityDefinition = de $ do
    lab iNDCCASecureDefinitionLabel
    let t = "t"
    s ["A", symmetricCryptosystem, "is called", iNDCCASecure', "if no feasible", adversary, "has a non-negligible", advantage, "in a", m t <> "-message", indistinguishabilityChosenCiphertextAttack, "game", "where", m t, "is only bounded by the adversary's running time"]


pseudoRandomGeneratorDefinition :: Note
pseudoRandomGeneratorDefinition = de $ do
    lab pseudoRandomGeneratorDefinitionLabel
    lab pRGDefinitionLabel
    let k = "k"
        n = "n"
    s ["A", pseudoRandomGenerator', "(" <> pRG' <> ")", "is a function", m $ fun gen_ (bitss k) (bitss n), "for", m $ n > k, "such that no feasible algorithm has a non-negligible advantage in distinguishing pseudo-randomly generated bits from actually random bits"]


blockCipherDefinition :: Note
blockCipherDefinition = do
    let f_ = "F"
    de $ do
        lab blockCipherDefinitionLabel
        lab blockLengthDefinitionLabel
        let n_ = "n"
            m_ = "m"
            f  = fn2 f_
            k_ = "k"
        s ["A", blockCipher', "with", blockLength', m n_, "and key length", m m_, "is a", function, m $ fun2 f_ (bitss n_) (bitss m_) (bitss n_), "such that for every key", m k_ <> ", ", m $ f cdot_ k_, "is a bijection"]
    nte $ do
        s ["Practicality requires that one knows efficient algorithms for computing ", m f_, "and its", inverse, "given the key"]

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

    s ["A", mAC, function, "is called", cMASecure', "if no feasible", adversary, "wins this game with a non negligible", probability]


