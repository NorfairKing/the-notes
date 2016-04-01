{-# LANGUAGE QuasiQuotes #-}
module Cryptography.Main where

import           Notes                                    hiding (cyclic,
                                                           inverse)

import qualified Data.ByteString                          as SB
import qualified Data.ByteString.Char8                    as SB8
import qualified Data.Text                                as T

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Inverse.Macro
import           Functions.Inverse.Terms
import           Functions.Jections.Terms
import           Groups.Macro
import           Groups.Terms
import           LinearAlgebra.VectorSpaces.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Probability.ConditionalProbability.Macro
import           Probability.Independence.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Terms
import           Relations.Orders.Macro
import           Sets.Basics.Terms

import           Cryptography.BlockCipherECBAttack
import           Cryptography.Macro
import           Cryptography.ManyTimePadAttack
import           Cryptography.OTP.Impl
import           Cryptography.SystemAlgebra
import           Cryptography.Terms

cryptography :: Note
cryptography = chapter "Cryptography" $ do
    section "Symmetric cryptosystems" $ do
        cryptographicSchemeDefinition
        cryptographicProtocolDefinition
        symmetricCryptosystemDefinition
        deterministicCryptoSystem
        cipherDefinition


        subsection "IND-CPA" $ do
            indcpaDefinition
            indcpaSecurityDefinition
            advantageNote
            securityDefinitionNote
            nonAdaptiveINDCPAGame
            nonAdaptiveINDCPASecurity
            nonAdaptiveINDCPAStrictlyWeaker
            deterministicCryptoSystemInsecure

        subsection "IND-CCA" $ do
            indccaDefinition
            indccaSecurityDefinition

        subsection "One Time Pad" $ do
            oneTimePadDefinition
            oneTimePadExample
            xorUniform
            oneTimePadSecure

        manyTimePadInsecure
        keyStreamGeneratorDefinition
        additiveStreamCipherDefinition

        subsection "pseudorandomness" $ do
            pseudoRandomGeneratorDefinition

        subsection "block ciphers" $ do
            blockCipherDefinition
            eCBDefinition
            eCBInsecure
            cBCDefinition
            counterDefinition

            xorBlockCipher


    section "Message Authentication Codes" $ do
        messageAuthenticationCodeDefinition
        messageAuthenticationCodeSecurityDefinition

    section "Key agreement" $ do
        diffieHellmanProtocolDefinition
        diffieHellmanManInTheMiddleAttack

    section "Computational Problems" $ do
        discreteLogarithmProblemDefinition
        computationalDHProblemDefinition
        diffieHellmanTripleDefinition
        decisionalDHProblemDefinition

    section "Public key encryption" $ do
        publicKeyEncryptionSchemeDefinition
        iNDCCASecureDefinitionPKEDefinition
        pKEINDCCASecureDefinition
        diffieHellmanPKEDefinition
        elGamalSchemeDefinition
        elGamalSchemeCPAButNotCCPASecure

    section "Trapdoor one-way permutations" $ do
        trapdoorOneWayPermutationDefinition
        tWOPInversionGame
        ethRootComputation
        rSATWOPDefinition
        tWOPAsPKE

    section "Digital signatures" $ do
        digitalSignatureDefinition
        signatureForgeryGameDefinition
        digitalSignatureSecurity

    section "Hash functions" $ do
        hashFunctionDefinition
        collisionFindingGameDefinition
        collisionResistantDefinition

    systemAlgebraS

cryptographicSchemeDefinition :: Note
cryptographicSchemeDefinition = de $ do
    lab cryptographicSchemeDefinitionLabel
    s ["A", cryptographicScheme', or, cryptosystem', "consists of several", functions]

cryptographicProtocolDefinition :: Note
cryptographicProtocolDefinition = de $ do
    lab cryptographicProtocolDefinitionLabel
    lab protocolDefinitionLabel
    s ["A", cryptographicProtocol', "for a given", set, "of", parties', "(" <> agents' <> ")", "consists of, for each", party <> ", a precicely specified behavior in the interaction with the other parties"]

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
        s [the, defineTerm "correctness condition", "states that the following must hold"]
        ma $ fa (k ∈ ksp_)
           $ fa (m ∈ msp_)
           $ fa (r ∈ rsp_)
           $ dec (enc m k r) k =: m
    nte $ do
        s ["Practicality dictates that", m enc_, and, m dec_, "must be efficiently computable"]
        s ["This is called the", defineTerm "practicality condition"]

deterministicCryptoSystem :: Note
deterministicCryptoSystem = de $ do
    s ["A", deterministic', cryptosystem, "is a system in which the", randomnessSpace, "is entirely ignored (or is the empty set, for example)"]
    s ["We then model the", encryptionFunction, "as taking only two arguments and leave out the", randomnessSpace]

cipherDefinition :: Note
cipherDefinition = de $ do
    lab cipherDefinitionLabel
    s ["A", cipher', "is a", deterministic, symmetricCryptosystem]

oneTimePadDefinition :: Note
oneTimePadDefinition = de $ do
    lab oneTimePadDefinitionLabel
    lab manyTimePadDefinitionLabel

    let n = "n"
    s [the, oneTimePad', "of some size", m n, "is a", cipher, "with", messageSpace, m (bitss n) <> ",", keySpace, m $ bitss n, and, "the following", encryptionFunction, and, decryptionFunction]
    let mesg = "m"
        k = "k"
    ma $ enc' mesg k =: mesg ⊕ k
    let c = "c"
    ma $ dec c k =: c ⊕ k

    tikzFig "One-Time Pad" [] $ raw $ [litFile|src/Cryptography/OTPTikZ.tex|]

    s [the, oneTimePad, "must only be used at most once for every key, otherwise it is called a", manyTimePad']

    toprove_ "prove that this is in fact a cipher, that the functions invert each other."

oneTimePadExample :: Note
oneTimePadExample = ex $ do
    let mesg :: String
        mesg = "Hello!"

        mesgBS :: SB.ByteString
        mesgBS = SB8.pack mesg

    keyBS <- getKeyFor mesgBS

    s ["Encrypting the", message, quoted $ raw $ T.pack mesg, "(encoded with ASCII) with following the", oneTimePad, cipher, "with a random key, results in the following situation"]

    let encryption = otpEncrypt keyBS mesgBS
    let showNice = text . raw . T.pack
    ma $ belowEachOther [RightColumn, LeftColumn]
        [ "message"     & showNice (hexBS' mesgBS)
        , "key"         & showNice (hexBS' keyBS)
        , "ciphertext"  & showNice (hexBS' encryption)
        ]

    ma $ belowEachOther [RightColumn, LeftColumn]
        [ "message"     & showNice (binBS' mesgBS)
        , "key"         & showNice (binBS' keyBS)
        , "ciphertext"  & showNice (binBS' encryption)
        ]

xorUniform :: Note
xorUniform = thm $ do
    lab xorUniformTheoremLabel
    s ["Let", m grp_, "be a", finite, group]
    let x = "X"
        y = "Y"
    s ["Let", m x, and, m y, "be two", independent, randomVariables, "over", m grps_]
    s ["If", m x, "is uniformly distributed, then", m $ x ** y, "is uniformly distributed"]

    proof $ do
        let g = "g"
        s ["Let", m g, "be an arbitrary", element, "of", m grps_]

        let i = "i"
            h=  "h"
        aligneqs (prob $ x ** y =: g)
            [ sumcmp (i ∈ g) $ prob $ x =: i ∧ x ** y =: g
            , sumcmp (i ∈ g) $ prob $ x =: i ∧ y =: ginv i ** g
            , sumcmp (i ∈ g) $ prob (x =: i) * prob (y =: ginv i ** g)
            , (1 /: setsize grps_) * sumcmp (i ∈ g) (prob $ y =: ginv i ** g)
            , (1 /: setsize grps_) * sumcmp (h ∈ g) (prob $ y =: h)
            , 1 /: setsize grps_
            ]

        s ["In the third step we used that", m x, and, m y, "are", independent, "and in the fifth step we substited", m h, "for", m $ ginv i ** g]
        why_ "Can we make this substitution?"
        s ["This means that", m $ x ** y, "is uniformly distributed"]


oneTimePadSecure :: Note
oneTimePadSecure = prop $ do
    let n = "n"
    s [the, oneTimePad <> "'s", ciphertexts, "are", independent, "of their", messages, "for a given message length", m n]
    proof $ do
        let m_ = "M"
            k_ = "K"
            c_ = "C"
            n = "n"
        s ["Let", m m_ <> ",", m k_, and, m c_, "denote", m n <> "-bit", randomVariables, "corresponding to the", plaintext <> ",", key, and, ciphertext, "respectively"]
        let mesg = "m"
            k = "k"
            c = "c"
        s ["Because the", key, m k_, "is uniformly distributed, so is the", ciphertext, "for every choice", m $ m_ =: mesg, "of the", message, ref xorUniformTheoremLabel]

        ma $ prob (k_ =: k) =: 2 ^ (- n)
        ma $ fa (mesg ∈ m_) $ prob (c_ =: enc' mesg k)

        s ["In other words, the following holds"]
        ma $ cprob (c_ =: c) (m_ =: mesg) =: 2 ^ (- n)
        ma $ prob (c_ =: c) =: 2 ^ (- n)

        s ["Now we see that for any uniformly generated", key, "the", plaintext, message, "and the", ciphertext, "are", independent]
        ma $ prob (cs [c_ =: c, m_ =: mesg]) =: cprob (c_ =: c) (m_ =: mesg) * prob (m_ =: mesg) =: prob (c_ =: c) * prob (m_ =: mesg)


keyStreamGeneratorDefinition :: Note
keyStreamGeneratorDefinition = do
    todo "Define a keystream generator"



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
    lab adversaryDefinitionLabel
    lab challengerDefinitionLabel
    lab attackerDefinitionLabel
    let t = "t"
        k = "k"
        i = "i"
    let b = "b"
        mb = "m" !: b
        c = "c"
    let b' = b <> "'"
    s ["A", m t <> "-message", indistinguishabilityChosenPlaintextAttack', "game", "(" <> iNDCPA' <> ")", "between a", challenger', "and an", adversary', "(" <> attacker' <> ")", "goes as follows"]
    enumerate $ do
        item $ s ["The challenger chooses a secret key", m k, "uniformly at random"]
        let mi = "m" !: i
            r = "r"
            ri = r !: i
        item $ s ["The adversary can choose up to", m t, messages, m mi, "and receive their encryptions", m $ enc mi k ri, "for fresh and independent randomness values", m $ ri ∈ rsp_]
        let m0 = "m" !: 0
            m1 = "m" !: 1
        item $ s ["The adversary chooses two", messages, m m0, and, m m1, "of the same length"]
        item $ s ["The challenger chooses a uniformly random bit", m b <> ", computes the encryption of ", m $ c =: enc mb k r, "for a fresh and independent randomness value", m $ r ∈ rsp_, "and returns it to the adversary"]
        item $ s ["The adversary can again choose up to", m t, messages, "as in step 2, but the total number is limited by", m t]
        item $ s ["The adversary issues his guess", m b', "for", m b]
    s [the, advantage', "of the adversary in this game is defined as", m $ abs $ 2 * prob (b' =: b) - 1 /: 2]

advantageNote :: Note
advantageNote = nte $ do
    s ["Note that this definition of the", advantage, "captures the idea that a non-zero advantage means that the", adversary, "is better than random"]

securityDefinitionNote :: Note
securityDefinitionNote = nte $ do
    s ["We could have defined security by saying that an", adversary, "should not be able to guess a single bit of information about the", plaintext, "from the", ciphertext <> ", but that definition has some problems"]
    s ["As an example, here we describe a", symmetricCryptosystem, "that fullfils this definition, but where the XOR of all", message, "bits is trivially computable"]
    s ["As such this scheme is not", iNDCPASecure]
    s ["Let the", keySpace, and, messageSpace, "both be", m $ bitss 2, "and let the", ciphertextSpace, "be", m $ bitss 3]
    let mesg = "m"
        m1 = mesg !: 1
        m2 = mesg !: 2
        k = "k"
        k1 = k !: 1
        k2 = k !: 2
    s [the, encryptionFunction, "encrypts a", message, m $ mesg =: tuple m1 m2 ∈ bitss 2, "using a", key, m $ k =: tuple k1 k2 ∈ bitss 2, "as follows"]
    ma $ enc' mesg k =: triple (m1 `xor` k1) (m2 `xor` k2) (m1 `xor` m2) ∈ bitss 3
    s [the, adversary, "can simply read off the XOR of the", message, "as the last bit of the", ciphertext]
    s ["Observe that this doesn't contradict the fact that any", ciphertext, "is still statistically", independent, "from its", plaintext, message]
    proof $ do
        let c = "c"
            c_ = "C"
            k_ = "K"
            m_ = "M"
            m1_ = m_ !: 1
            m2_ = m_ !: 2
        s ["We will prove that", m c_, "is statistically", independent, "from", m m1_, "under the assumption that", m m_, and, m k_, "are", independent, "and uniformly distributed", randomVariables, "over", m $ bitss 2]
        s ["This will imply that", m c_, "is statistically", independent, "from", m m2_, "as well and as such from", m m_]
        aligneqs (cprob (c_ =: c) (m1_ =: m1))
            [ sumcmp (cs [m2 ∈ bits, k ∈ bitss 2]) $ cprob (c_ =: c ∧ m2_ =: m2 ∧ k_ =: k) (m1_ =: m1)
            , sumcmp (cs [m2 ∈ bits, k ∈ bitss 2]) $ cprob (m2_ =: m2) (m1_ =: m1)
                                                   * cprob (k_ =: k) (m_ =: tuple m1 m2)
                                                   * cprob (c_ =: c) (m_ =: tuple m1 m2 ∧ k_ =: k)
            , sumcmp (cs [m2 ∈ bits, k ∈ bitss 2]) $ prob (m2_ =: m2)
                                                   * prob (k_ =: k)
                                                   * cprob (c_ =: c) (m_ =: tuple m1 m2 ∧ k_ =: k)
            , (2 ^ (-3)) * sumcmp (cs [m2, k]) (cprob (c_ =: c) (m_ =: tuple m1 m2 ∧ k_ =: k))
            , (2 ^ (-3))
            ]
        why_ "does the second step hold?"
        s ["In step four, we use that", keys, "are assumed to be distributed uniformly"]
        s ["We also used that, because", m m_, "is assumed to be distributed uniformly,", m m2_, "is", independent, "from", m m1_]
        s ["In the last step we used that, because", m c_, "is completely determined given", m m_, and, m k]
        why_ "shouldn't all the terms in that sum evaluate to 1?"
        s ["The above shows that", m c_, "is uniformly distributed given", m $ m1_ =: m1]
        s ["It now follows that", m c_, and, m m1_, "are statistically", independent]
        aligneqs (prob $ c_ =: c)
            [ sumcmp (m1 ∈ bits) (prob (m1_ =: m1) * cprob (c_ =: c) (m1_ =: m1))
            , (2 ^ (-3)) * sumcmp (m1 ∈ bits) (prob $ m1_ =: m1) =: 2 ^ (-3)
            ]
        s ["Consequently.."]
        ma $ prob (m1_ =: m1 ∧ c_ =: c) =: prob (m1_ =: m1) * cprob (c_ =: c) (m1_ =: m1) =: prob (m1_ =: m1) * prob (c_ =: c)

indcpaSecurityDefinition :: Note
indcpaSecurityDefinition = de $ do
    lab iNDCPASecureDefinitionLabel
    let t = "t"
    s ["A", symmetricCryptosystem, "is called", iNDCPASecure', "if no feasible", adversary, "has a non-negligible", advantage, "in a", m t <> "-message", indistinguishabilityChosenPlaintextAttack, "game", "where", m t, "is only bounded by the adversary's running time"]

nonAdaptiveINDCPAGame :: Note
nonAdaptiveINDCPAGame = de $ do
    lab nonAdaptiveINDCPADefinitionLabel
    let mp = tuple ("m" !: 0) ("m" !: 1)
    s ["A", nonAdaptiveINDCPA', "game between a", challenger, and, adversary, "is played as follows for a fixed message pair", m mp]
    let b = "b"
    let b' = "b'"
    enumerate $ do
        let k = "k"
        item $ s [the, challenger, "chooses a", secretKey, m k, "uniformly at random"]
        let c = "c"
            r = "r"
        item $ s [the, challenger, "chooses a uniformly random bit", m b <> ", computes the encryption", m $ c =: enc ("m" !: b) k r, "for a fresh and", independent, "randomness value", m $ r ∈ rsp_, "and sends", m c, "to the", adversary]
        item $ s [the, adversary, "can choose messages and receive their encryptions"]
        item $ s [the, adversary, "guesses", m b, "by issuing a guess", m b']
    s [the, advantage, "of the adversary in this game is defined as", m $ 2 * prob (b' =: b) - 1 /: 2]

nonAdaptiveINDCPASecurity :: Note
nonAdaptiveINDCPASecurity = de $ do
    lab nonAdaptivelyINDCPASecureDefinitionLabel
    s ["A", symmetricCryptosystem, "is called", nonAdaptivelyINDCPASecure', "if for every fixed pair of messages of the same length, no feasible adversary has a non-negligible", advantage, "in the", nonAdaptiveINDCPA, "game"]

nonAdaptiveINDCPAStrictlyWeaker :: Note
nonAdaptiveINDCPAStrictlyWeaker = thm $ do
    s [nonAdaptiveINDCPA, "security is strictly weaker than regular", iNDCPA, "security"]

    proof $ do
        s ["Every", iNDCPASecure, symmetricCryptosystem, "is also", nonAdaptivelyINDCPASecure, "and if there exists a", nonAdaptivelyINDCPASecure, symmetricCryptosystem, "then there is one such system that is not", iNDCPASecure]
        let m0 = "m" !: 0
            m1 = "m" !: 1
        enumerate $ do
            item $ do
                let a = "A"
                    a' = a <> "'"
                let e = epsilon
                s ["First we prove that if there exists an", adversary, "with non-negligible", advantage, m e, "in winning the", nonAdaptiveINDCPA, "game for a fixed", message, "pair", m $ tuple m0 m1, "of the same length, then there exists an", adversary, m a', "that wins the", nonAdaptiveINDCPA, "game with advantage", m e]
                s ["Indeed, the new", adversary, m a', "simply skips steps 2 of the", iNDCPA, "game and submits the fixed", message, "pair", m $ tuple m0 m1, "in step 3"]
                s ["Then", m a', "does exactly what", m a, "does so they have the same", advantage]
            item $ do
                s ["Next we show that there exists a", nonAdaptivelyINDCPASecure, symmetricCryptosystem, "that is not", iNDCPASecure]
                s ["Let", m $ tuple enc_ dec_, "denote the assumed", nonAdaptivelyINDCPASecure, symmetricCryptosystem, "with", messageSpace, m msp_ <> ",", ciphertextSpace, m csp_ <> ",", keySpace, m ksp_, and, randomnessSpace, m rsp_]

                let e_ = "e'"
                    d_ = "d'"
                    e = fn3 e_
                    d = fn2 d_
                s ["We define the follwing", symmetricCryptosystem, m $ tuple e_ d_, "with", keySpace, m $ ksp_ ^ 2, and, ciphertextSpace, m $ csp_ ⨯ ksp_ ⨯ bits, "as follows"]

                let r = "r"
                    k = "k"
                    k1 = k !: 1
                    k2 = k !: 2
                    mesg = "m"
                ma $ e mesg (tuple k1 k2) r =: cases ( do
                        triple (enc mesg k1 r) k2 1 <> text " if " <> mesg =: k2
                        lnbk
                        triple (enc mesg k1 r) k2 0 <> text " if " <> mesg `neq` k2
                    )
                let b = "b"
                    c = "c"
                    x = "x"
                ma $ d (triple c k b) (tuple k1 k2) =: dec c k1

                s ["First we prove that this is in fact a valid", symmetricCryptosystem]
                s ["Let", m $ tuple k1 k2 ∈ ksp_ ^ 2, "be an arbitrary", key <> ",", m $ mesg ∈ msp_, "an arbitrary", message, and, m $ r ∈ rsp_, "an arbitrary randomness value"]
                aligneqs (d (e mesg (tuple k1 k2) r) (tuple k1 k2))
                    [ d (triple (enc mesg k1 r) k2 x) (tuple k1 k2)
                    , dec (enc mesg k1 r) k1
                    , mesg
                    ]
                s ["In the above,", m x, "is a bit"]

                s ["We now show that this scheme is", nonAdaptivelyINDCPASecure]
                s ["Let", m $ tuple m0 m1, "be an arbitrary fixed", message, "pair"]
                s ["Let", m $ tuple k1 k2, "be a", key, "chosen independently of the", message, "pair and uniformly at random"]
                s ["Observe firstly that the", probability, "that", m k2, "matches either of the", messages, "is negligible for large", keySpaces, m ksp_, ref unionBoundTheoremLabel]
                ma   $ prob (m0 =: k2 ∨ m1 =: k2)
                    <= prob (m0 =: k2) + prob (m1 =: k2)
                    =: (2 /: setsize ksp_)
                let cb = c !: b
                    cb' = cb <> "'"
                    mb = mesg !: b
                s ["If", m m0, and, m m1, "are both different from", m k2, "the challenger outputs", m $ cb' =: triple (enc mb k1 r) k2 0, "and since that", m k2, "is", independent, "of", m b <> ",", m k1, and, m r <> ",", "this does not reveal any more information about", m b, "than", m $ cb =: enc mb k r]
                s ["Since no", adversary, "can guess", m b, "from", m cb, "with non-negligible", advantage <> ", the scheme", m $ tuple e_ d_, "is", nonAdaptivelyINDCPASecure]

                s ["However, the following", adversary, "wins the regular", iNDCPA, "game for this scheme with", advantage, "tending to", m 1, "for large", keySpaces]
                itemize $ do
                    item $ s [the, adversary, "queries the encryption for some", message, m mesg, "and obtains the responce", m $ c =: (triple (enc mesg k1 r) k2 x) ∈ (csp_ ⨯ ksp_ ⨯ bits)]
                    let m' = mesg <> "'"
                        xb = "x" !: b
                    item $ s [the, adversary, "issues the challenge", m $ tuple k2 m', "for some arbitrary", m $ m' `neq` k2, "and", m $ len m' =: len k2, "and obtains", m $ cb' =: triple cb k2 xb, "from the", challenger]
                    item $ s [the, adversary, "outputs", m 0, "if", m $ xb =: 1, and, m 1, "otherwise"]
                s ["The inherent difference between", nonAdaptiveINDCPASecurity, and, iNDCPA, "security is that the", adversary, "can aqcuire information before the challenge is submitted and can use that information in the challenge"]









indccaDefinition :: Note
indccaDefinition = de $ do
    lab iNDCCADefinitionLabel
    lab indistinguishabilityChosenCiphertextAttackDefinitionLabel
    let t = "t"
        k = "k"
    let b = "b"
        mb = "m" !: b
        c = "c"
    let b' = b <> "'"
    s ["A", m t <> "-message", indistinguishabilityChosenPlaintextAttack', "game", "(" <> iNDCCA' <> ")", "between a", challenger, "and an", adversary, "goes as follows"]
    enumerate $ do
        item $ s ["The challenger chooses a secret key", m k, "uniformly at random"]
        let i = "i"
        let mi = "m" !: i
            ci = "c" !: i
            r = "r"
            ri = r !: i
        item $ s ["The adversary can choose up to", m t, messages, m mi, or, ciphertexts, m ci, "and receive their encryptions", m $ enc mi k ri, "for fresh and independent randomness values", m $ ri ∈ rsp_, or, ciphertexts, "(in the case of", messages <> ") or receive their decryptions", m $ dec ci k, "(in the case of", ciphertexts <> ")"]
        let m0 = "m" !: 0
            m1 = "m" !: 1
        item $ s ["The adversary chooses two", messages, m m0, and, m m1, "of the same length"]
        item $ s ["The challenger chooses a uniformly random bit", m b <> ", computes the encryption of ", m $ c =: enc mb k r, "for a fresh and independent randomness value", m $ r ∈ rsp_, "and returns it to the adversary"]
        item $ s ["The adversary can again choose up to", m t, messages, or, ciphertexts, "as in step 2, but the total number is limited by", m t]
        item $ s ["The adversary issues his guess", m b', "for", m b]
    s [the, advantage', "of the adversary in this game is defined as", m $ 2 * prob (b' =: b) - 1 /: 2]

indccaSecurityDefinition :: Note
indccaSecurityDefinition = de $ do
    lab iNDCCASecureDefinitionLabel
    let t = "t"
    s ["A", symmetricCryptosystem, "is called", iNDCCASecure', "if no feasible", adversary, "has a non-negligible", advantage, "in a", m t <> "-message", indistinguishabilityChosenCiphertextAttack, "game", "where", m t, "is only bounded by the adversary's running time"]

manyTimePadInsecure :: Note
manyTimePadInsecure = do
    thm $ do
        lab manyTimePadInsecureTheoremLabel
        s ["Re-using the key for a", oneTimePad <> ", thus yielding a so-called", manyTimePad, "is not", iNDCPASecure]

        proof $ do
            s ["We will prove an even stronger statement, namely that the", manyTimePad, "is not even secure in a", iNDCPA, "game where the initial messages cannot be used during the challenge"]
            enumerate $ do
                item $ s ["An", attacker, "can gain an", advantage, "of", m 1, "by playing a", m 2 <> "-message", iNDCPA, "-game as follows"]
                let m0 = "m" !: 0
                    m1 = "m" !: 1
                    m2 = "m" !: 2
                    c = "c"
                    c0 = c !: 0
                    c1 = c !: 1
                item $ s [the, attacker, "chooses two distinct", messages, m m0, and, m m1, "of the same length at random and asks for their encryptions", m c0, and, m c1]
                item $ s [the, attacker, "then submits", m $ (c0 `xor` c1) =: (m0 `xor` m1), "as well as another random", message, m m2, "and receives a", ciphertext, m c, "from the", challenger]
                item $ do
                    s [the, attacker, "computes", m $ c `xor` c0]
                    s [the, attacker, "checks whether this equals", m m1]
                    s ["If so, he outputs the bit", m 0, ", otherwise he will output the bit", m 1]
                    s ["This way the", attacker, "wins the game every time"]

    nte $ do
        let t = "t"
        s ["Note that we cannot say that the", oneTimePad, "is", iNDCPASecure, "nor", iNDCCASecure, "for any", m $ t >= 1, "because the", oneTimePad, "can, by definition, only be used once for the same key"]

    manyTimePadAttack


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
        s ["Practicality requires that one knows efficient algorithms for computing ", m f_, "and its", inverseFunction, "given the key"]

eCBDefinition :: Note
eCBDefinition = de $ do
    lab electronicCodebookDefinitionLabel
    lab eCBDefinitionLabel
    let f_ = "F"
        k_ = "k"
        n = "n"
    s ["Let", m f_, "be a", blockCipher, "with", blockLength, m n, "and let", m k_, "be a key sampled uniformly from the key space"]
    s [the, electronicCodebook', "(" <> eCB' <> ")", "mode for a", blockCipher, "is a", cipher, "as follows"]
    let mesg = "m"
        f = fn2 f_
        l = "l"
    s ["Let", m mesg, "be a", message, "with a length that is a multiple of", m n <> ": ", m $ l * n]
    itemize $ do
        item $ s ["Encryption: ", m $ enc' mesg k_ =: f (mesg !: 1) k_ ++ f (mesg !: 2) k_ ++ dotsc ++ f (mesg !: l) k_]
        let c = "c"
            fm = fn2 $ inv f_
        item $ s ["Decryption: ", m $ dec c k_ =: fm (c !: 1) k_ ++ fm (c !: 2) k_ ++ dotsc ++ fm (c !: l) k_]

    tikzFig "ECB mode" [] $ raw $ [litFile|src/Cryptography/ECBTikZ.tex|]


eCBInsecure :: Note
eCBInsecure = do
    thm $ do
        let f_ = "F"
            n = "n"
        s ["Let", m f_, "be a", blockCipher, "with", blockLength, m n]
        -- let k_ = "k"
        s [the, electronicCodebook', "mode for a", blockCipher, "is not", iNDCCASecure, "on its own"]

        proof $ do
            s ["We will prove an even stronger statement, namely that the", electronicCodebook, "mode is not even secure in a", iNDCPA, "game where the initial messages cannot be used during the challenge"]
            s ["An", attacker, "can gain an", advantage, "of", m 1, "by playing a", m 0 <> "-message", iNDCPA, "-game as follows"]
            enumerate $ do
                let m0 = "m" !: 0
                    m1 = "m" !: 1
                item $ s [the, attacker, "chooses two", messages, m m0, and, m m1, "of length", m $ 2 * n, "such that the following holds"]
                itemize $ do
                    item $ s ["In ", m m0, "both blocks are equal"]
                    item $ s ["In ", m m1, "the blocks are distinct"]
                let c = "c"
                item $ s [the, attacker, "then submits", m m0, and, m m1, "and receives a", ciphertext, m c, "from the", challenger]
                item $ s [the, attacker, "outputs the bit", m 0, "if the blocks of", m c, "are equal", and, m 1, "otherwise"]

    blockCipherECBAttack

cBCDefinition :: Note
cBCDefinition = de $ do
    lab cipherBlockChainingDefinitionLabel
    lab cBCDefinitionLabel
    let f_ = "F"
        k_ = "k"
        n = "n"
    s ["Let", m f_, "be a", blockCipher, "with", blockLength, m n, "and let", m k_, "be a key sampled uniformly from the key space"]
    s [the, cipherBlockChaining', "(" <> cBC' <> ")", "mode for a", blockCipher, "is a", symmetricCryptosystem, "as follows"]
    let mesg = "m"
        f = fn2 f_
        l = "l"
    s ["Let", m mesg, "be a", message, "with a length that is a multiple of", m n <> ": ", m $ l * n]
    itemize $ do
        let c = "c"
            c0 = c !: 0
            c1 = c !: 1
            cl = c !: l
        item $ do
            "Encryption: "
            let iv = "IV"
            s ["First a so-called", initialisationVector', m c0, "(also written as", m iv <> ")", "is chosen uniformly at random"]
            ma $ enc mesg k_ c0
                 =: c0
                 ++ f (mesg !: 1 `xor` c0) k_
                 ++ f (mesg !: 2 `xor` c1) k_
                 ++ dotsc
                 ++ f (mesg !: l `xor` cl) k_

        let fm = fn2 $ inv f_
        item $ do
            s ["Decryption must be done sequentially"]
            ma $ dec c k_
                =: (fm (c !: 1) k_ `xor` c0)
                ++ (fm (c !: 2) k_ `xor` c1)
                ++ dotsc
                ++ (fm (c !: l) k_ `xor` cl)


    tikzFig "CBC mode" [] $ raw $ [litFile|src/Cryptography/CBCTikZ.tex|]


counterDefinition :: Note
counterDefinition = de $ do
    lab counterDefinitionLabel
    lab cTRDefinitionLabel
    let f_ = "F"
        k_ = "k"
        n = "n"
    s ["Let", m f_, "be a", blockCipher, "with", blockLength, m n, "and let", m k_, "be a key sampled uniformly from the key space"]
    s [the, counter', "(" <> cTR' <> ")", "mode for a", blockCipher, "is a", symmetricCryptosystem, "as follows"]
    let mesg = "m"
        f = fn2 f_
        l = "l"
    s ["Let", m mesg, "be a", message, "with a length that is a multiple of", m n <> ": ", m $ l * n]
    itemize $ do
        let c = "c"
            c1 = c !: 1
            c2 = c !: 1
            cl = c !: l
            i = "i"
            r = "r"
            bs = autoAngleBrackets
        item $ do
            "Encryption:"
            let iv = "IV"
            s ["First an", initialisationVector, m $ r ∈ bitss (n / 2), "(also written as", m iv <> ")", "is chosen uniformly at random"]
            ma $ enc mesg k_ r
                 =: r
                 ++ mesg !: 1 `xor` (f (r ++ bs 1) k_)
                 ++ mesg !: 2 `xor` (f (r ++ bs 2) k_)
                 ++ dotsc
                 ++ mesg !: l `xor` (f (r ++ bs l) k_)
            s ["Here", m $ bs i, "is the representation of", m i, "as an", m $ n / 2, "bit string"]

        item $ do
            "Decryption:"
            ma $ dec c k_
                =: c1 `xor` (f (r ++ bs 1) k_)
                ++ c2 `xor` (f (r ++ bs 2) k_)
                ++ dotsc
                ++ cl `xor` (f (r ++ bs l) k_)
    s ["Note that", m $ inv f_, "is not needed for decryption"]

    tikzFig "CTR mode" ["scale=1.5"] $ raw $ [litFile|src/Cryptography/CTRTikZ.tex|]


deterministicCryptoSystemInsecure :: Note
deterministicCryptoSystemInsecure = thm $ do
    s ["No", cipher, "could ever be", iNDCPASecure, "as is"]

    proof $ do
        s ["Let", m $ tuple enc_ dec_, "be a", cipher]
        s [the, attacker, "chooses two arbitrary", messages, "and submits them to receive two", ciphertexts]
        s [the, attacker, "then submits those same", messages, "as part of the challenge"]
        s [the, attacker, "then only needs to compare the", ciphertext, "he got to the", ciphertexts, "he got earlier to win the game with", advantage, m 1]
        s ["Note that this only works because a", cipher, "is defined to be deterministic"]


xorBlockCipher :: Note
xorBlockCipher = do
    thm $ do
        let f_ = "F"
            n = "n"
            k = "k"
        s ["Let", m $ fun2 f_ (bitss n) (bitss k) (bitss n), "be a", blockCipher]
        s ["If we know that", m f_, "can be implemented with only XOR gates and we have an encryption oracle, we can decrypt any", message]

        proof $ do
            let mesg = "m"
                c = "c"
                k = "k"
            s ["Let", m mesg, "be an arbitrary", message, "and let", m c, "be its encryption with a", secretKey, m k]
            s ["Because every XOR gate corresponds to summing to bits, every bit of", m c, "can be seen as a linear combination of the", message, "bits, the", key, "bits and a constant"]
            let i = "i"
                ci = c !: i
                q = "q"
                qi = q !: i
                j = "j"
                kj = k !: j
                mj = mesg !: j
                aij = "a" !: (i <> j)
                bij = "b" !: (i <> j)
            ma $ ci =: sumcmpr (j =: 1) n (aij * mj) + sumcmpr (j =: 1) k (bij * kj) + qi
            s ["In matrix notation this looks as follows"]
            let a = "A"
                b = "B"
            ma $ c =: a * mesg + b * k + q
            s ["Here", m a, "is an", m $ n × n, matrix <> ",", m b, "is an", m $ n × k, matrix, and, m q, "is a", vector, "of length", m n]
            newline

            let u = "u"
            s ["When we ask for the encryption of the zero message, we get", m $ u =: b * k + q]
            s ["Now we only need to find", m a]
            let mi = mesg !: i
                gi = "g" !: i
            s ["We ask for the encryptions", m gi, "of the", messages, m mi, "that are all zero except in place", m i, "to find the collumns of", m a]
            ma $ gi - u =: (pars $ a * mi + b * k + q) - u =: a * mi
            s [m $ a * mi, "is precicely the", m i <> "-th column of", m a]
            s ["We now know", m a, "and", m $ b * k + q]
            s ["Because", m f_, "is a", permutation, "for every", m k <> ",", m f_, "must be", invertible]
            s ["We can therefore solve the linear system", m $ a * mesg =: c - u, "to find", m mesg, "from", m c]

    thm $ do
        let f_ = "F"
            n = "n"
            k = "k"
        s ["Let", m $ fun2 f_ (bitss n) (bitss k) (bitss n), "be a", blockCipher]
        s ["If we know that", m f_, "is operated in", cipherBlockChaining, "mode, can be implemented with only XOR gates and we have an encryption oracle, we can decrypt any", message]
        toprove



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

discreteLogarithmProblemDefinition :: Note
discreteLogarithmProblemDefinition = de $ do
    lab discreteLogarithmDefinitionLabel
    lab dLDefinitionLabel
    let aa = "A"
        a = "a"
        g = "g"
    s [the, discreteLogarithm', "(" <> dL' <> ")", "problem", "for a", cyclic_, group, m $ grp_ =: grp (genby g) grpop_, "is the problem of computing, for a given", group, element, m $ aa ∈ grps_, "the exponent", m $ integer a, " such that", m $ aa =: g ^ a, "holds"]

computationalDHProblemDefinition :: Note
computationalDHProblemDefinition = de $ do
    lab computationalDiffieHellmanDefinitionLabel
    lab cDHDefinitionLabel
    let a = "a"
        b = "b"
        g = "g"
    s [the, computationalDiffieHellman, "(" <> cDH' <> ")", "problem for a given", cyclic, group, m $ grp_ =: grp (genby g) grpop_, "is the problem of computing, for given group elements", m $ g ^ a, and, m $ g ^ b, "the group element", m $ g ^ (a * b)]

diffieHellmanTripleDefinition :: Note
diffieHellmanTripleDefinition = de $ do
    lab diffieHellmanTripleDefinitionLabel
    let a = "a"
        b = "b"
        c = "c"
        g = "g"
    s ["A", diffieHellmanTriple, "in a given", cyclic, group, m $ grp_ =: grp (genby g) grpop_, "is a triple of the form", m $ triple (g ^ a) (g ^ b) (g ^ (a * b)), "where", m a <> ",", m b, and, m c, "are hole numbers"]


decisionalDHProblemDefinition :: Note
decisionalDHProblemDefinition = de $ do
    lab computationalDiffieHellmanDefinitionLabel
    lab cDHDefinitionLabel
    let a = "a"
        b = "b"
        c = "c"
        g = "g"
    s [the, decisionalDiffieHellman', "(" <> dDH' <> ")", "problem for a given", cyclic, group, m $ grp_ =: grp (genby g) grpop_, "is the problem of determining whether, for given group elements", (m $ g ^ a) <> ",", m $ g ^ b, and, m $ g ^ c, "whether they are chosen randomly and independently from", m grps_, "or form a", diffieHellmanTriple]


publicKeyEncryptionSchemeDefinition :: Note
publicKeyEncryptionSchemeDefinition = de $ do
    lab publicKeyEncryptionSchemeDefinitionLabel
    lab keyGeneratorDefinitionLabel
    s ["A", publicKeyEncryptionScheme', "(" <> pKE' <> ")", "consists of three functions"]
    itemize $ do
        item $ do
            s ["A", keyGenerator', function]
            s ["This is a probabillistic", function, "that generates a", keyPair' <> ",", "a", publicKey', anda, secretKey', "(" <> privateKey' <> ")"]
        item $ do
            s ["An", encryptionFunction']
            s ["This is a probabillistic", function, "that takes as inputs a", publicKey, anda, plaintext, "and computes the", ciphertext]
        item $ do
            s ["A", decryptionFunction']
            s ["This is a deterministic", function, "that takes as inputs a", secretKey, anda, ciphertext, "and computes the", plaintext]

    s ["... such that for every encryption/decryption", keyPair, "the decryption transformation is the inverse of the encryption transformation"]

    todo "formalize"


iNDCCASecureDefinitionPKEDefinition :: Note
iNDCCASecureDefinitionPKEDefinition = de $ do
    lab iNDCCADefinitionLabel
    lab indistinguishabilityChosenCiphertextAttackDefinitionLabel
    let t = "t"
    s ["A", m t <> "-message", indistinguishabilityChosenPlaintextAttack', "(" <> iNDCCA' <> ")", "game", "for a", publicKeyEncryptionScheme, "between a", challenger, "and an", adversary, "goes as follows"]
    let b = "b"
        b' = "b'"
    enumerate $ do
        item $ s [the, challenger, "chooses a", secretKey, publicKey, "pair using the", keyGenerator, function, "and sends the", publicKey, "to the adversary"]
        item $ s [the, adversary, "can choose", ciphertexts, "and receive their decryptions under the", secretKey]
        let m0 = "m" !: 0
            m1 = "m" !: 1
            mb = "m" !: b
        item $ s [the, adversary, "chooses two messages", m m0, and, m m1, "of the same length"]
        let b = "b"
        item $ s [the, challenger, "chooses a uniformly random bit", m b <> ", computes the encryption of", m mb <> ", and returns it to the", adversary]
        item $ s [the, adversary, "can again choose", ciphertexts, "and receive their decryptions as in step 2, but the encryption of", m mb, "is excluded"]
        item $ s [the, adversary, "guesses", m b, "by issuing a guess", m b']
    s [the, advantage', "of the", adversary, "in this game is defined as", m $ 2 * prob (b' =: b) - 1 /: 2]
    todo "formalize"

pKEINDCCASecureDefinition :: Note
pKEINDCCASecureDefinition = de $ do
    s ["A", publicKeyEncryptionScheme, "is called", iNDCCASecure, "if no feasible", adversary, "has a negligible", advantage]


diffieHellmanPKEDefinition :: Note
diffieHellmanPKEDefinition = de $ do
    s [the, diffieHellman, protocol, "can be used as a", publicKeyEncryptionScheme]
    let g = "g"
        q = "q"
    s ["Let", m $ grp_ =: grp (genby g) grpop_, "be a", cyclic, group, "with a known", order, m q, and, "let", m $ tuple enc_ dec_, "be a given secure", symmetricCryptosystem]
    s ["The following is then a", publicKeyEncryptionScheme]
    let zq = integers !: q
    itemize $ do
        let b = "B"
            x = "x"
            xb = x !: b
            mesg = "m"
        item $ do
            s ["A", keyGenerator, function]
            newline
            s ["Choose", m xb, "uniformly at random from", m zq]
            s [the, secretKey, "is", m xb, "and the", publicKey, "is", m $ g ^ xb]
        item $ do
            let r = "r"
            s ["An", encryptionFunction]
            newline
            s ["Choose", m x, "at random from", m zq]
            s [the, ciphertext, "for a", message, m mesg, "is the pair", m $ tuple (g ^ x) (enc mesg (g ^ (xb ^ x)) r), "where", m r, "is a uniformly random value from the", randomnessSpace, "of", m enc_]
        item $ do
            s ["A", decryptionFunction]
            newline
            todo "Left as exercise?"
    s ["Note that we implicitly use the fact every cyclic group of", finite, order, m q, "is isomorphic to", m zq]
    refneeded "prove this in the group chapter"


elGamalSchemeDefinition :: Note
elGamalSchemeDefinition = de $ do
    lab elGamalDefinitionLabel
    s ["A", publicKeyEncryptionScheme, "based on the", diffieHellman, protocol, "where the", symmetricCryptosystem, "is", the, oneTimePad, "is called the", elGamal', publicKeyEncryptionScheme]


elGamalSchemeCPAButNotCCPASecure :: Note
elGamalSchemeCPAButNotCCPASecure = thm $ do
    s [the, elGamal, publicKeyEncryptionScheme, "is", iNDCPASecure, "but not", iNDCCASecure]


trapdoorOneWayPermutationDefinition :: Note
trapdoorOneWayPermutationDefinition = de $ do
    lab trapdoorOneWayPermutationDefinitionLabel
    lab tWOPDefinitionLabel
    lab trapdoorGeneratorDefinitionLabel
    lab trapdoorDefinitionLabel
    let x = mathcal "X"
        y = mathcal "Y"
    s ["A", trapdoorOneWayPermutation', "(" <> tWOP <> ")", "is and efficient probabillistic algorithm, the", trapdoorGenerator', "which generates descriptions of two algorithms and two", sets, m x, and, m y]
    let f_ = "F"
        d_ = "D"
        g_ = "g"
        g = fn g_
    itemize $ do
        item $ do
            s ["An algorithm", m f_, "computing an", injective, function, m $ fun "f" x y]
            s ["Typically,", m f_, "is described by a short parameter called the", publicKey, "which also defines", m x, and,m y]
        item $ do
            s ["An algorithm", m d_, "computing the", inverseFunction, m g_, "of", m f_]
            ma $ fun g_ y (x ∪ bot) <> text " such that " <> (fa ("x" ∈ x) (g (fn "f" "x") =: "x"))
            s ["If", m "y", "is not in the range of", m f_, "then", m $ g "y", "will be", m bot]
            s ["Typically,", m d_, "is described by a short parameter called the", trapdoor']


tWOPInversionGame :: Note
tWOPInversionGame = de $ do
    s [the, tWOP, "inversion game between an", adversary, anda, challenger, "is defined as follows"]
    let x = mathcal "X"
        y = mathcal "Y"
        f = "F"
        d = "D"
    itemize $ do
        item $ do
            s [the, challenger, "uses the", trapdoorGenerator, "to generate", m $ quadruple f d x y, "and sends the", publicKey, "(" <> m (triple x y f) <> ")", "together with", m $ fn f "x", "for a uniformly random", m $ "x" ∈ x, "to the", adversary]
        item $ do
            s [the, adversary, "wins the game if she outputs", m "x"]


ethRootComputation :: Note
ethRootComputation = do
    thm $ do
        let gid_ = "1"
        s ["Let", m grp_, "be some", finite, group, "with neutral element", m gid_]
        let e = "e"
            d = "d"
            gs = setsize grps_
        s ["Let", m $ integer e, "be given exponent", relativelyPrime_, "to", m gs]
        let x = "x"
            y = "y"
        s [the, m e <> "-th root of an", element, m $ y ∈ grps_, "namely", m $ x ∈ grps_, "satisfying", m (x ^ e =: y) <> ", can be computed according to", m $ x =: y ^ d, "where", m $ d =: ginvm (intmgrp gs) e, "is the multiplicative inverse of", m e, "modulo", m gs]
        proof $ do
            let k = "k"
            s ["Define", m $ k =: ((e * d - 1) /: gs), "and observe the following"]
            ma $
                (pars $ x ^ e) ^ d
                =: x ^ (e * d)
                =: x ^ (k * gs + 1)
                =: (pars (x ^ gs)) ^ k ** x
                =: x
            s ["Here we used the fact that", m $ x ^ gs, "equals", m gid_, "because the", order, "of", m x, "divides", m gs, ref elementOrderDividesGroupOrderTheoremLabel]
    nte $ do
        s ["No general algorithm is known for computing", m "e" <> "-th roots in a", group, "without knowing its", order]

rSATWOPDefinition :: Note
rSATWOPDefinition = de $ do
    s [the, rSA', trapdoorOneWayPermutation, "is defined as follows"]
    let p = "p"
        q = "q"
        n = "n"
        e = "e"
        d = "d"
    s [the, trapdoorGenerator, "chooses two", primes, m p, and, m q, "computes", m $ n =: p * q, "and chooses", m e, "such that", m e, "is", relativelyPrime_, "to", m $ etot n]
    s [the, publicKey, "is the pair", m $ tuple n e]
    s ["It then computes", m $ d =: e ^ (-1) `mod` etot n]
    s [the, trapdoor, "is", m d]
    let z = int0mod n
        x = mathcal "X"
        y = mathcal "Y"
    s ["It outputs", m $ x =: y =: z, "as the relevant", sets]
    let f = "f"
        g = "g"
        x = "x"
    s [m f, "is defined as", m $ func f z z x (x ^ e), and, m g, "is defined as", m $ func g z z x (x ^ d)]

    todo "prove that this is in fact secure"


tWOPAsPKE :: Note
tWOPAsPKE = de $ do
    s ["Given a", trapdoorOneWayPermutation <> ", we can construct a", publicKeyEncryptionScheme, "as follows"]
    s ["Let the domain of the", trapdoorOneWayPermutation, "be the", messageSpace]
    let f_ = "F"
        d_ = "D"
    s ["Let encryption be the application of the", trapdoorOneWayPermutation <> ", where the", publicKey, "is the description of the algorithm", m f_, "and the", secretKey, "the description of the algorithm", m d_]


digitalSignatureDefinition :: Note
digitalSignatureDefinition = de $ do
    lab digitalSignatureSchemeDefinitionLabel
    lab dSSDefinitionLabel
    lab signingKeyDefinitionLabel
    lab signatureVerificationKeyDefinitionLabel
    lab signingAlgorithmDefinitionLabel
    lab signatureDefinitionLabel
    lab signatureVerificationAlgorithmDefinitionLabel
    s ["A", digitalSignatureScheme', "consists of three algorithms as follows"]
    itemize $ do
        item $ s ["A probabillistic", keyGenerator', "algorithm which generates a", keyPair <> ", consisting of a", signingKey', "(" <> secretKey <> ")", "and a", signatureVerificationKey', "(" <> publicKey <> ")"]
        item $ s ["A probabillistic", signingAlgorithm', "that takes as inputs a", signingKey, anda, message, "and computes the", signature', "for the", message]
        item $ s ["A deterministic", signatureVerificationAlgorithm', "that takes as inputs a", signatureVerificationKey <> ", a", message, anda, signature, "and outputs a bit that can be interpreted as", dquoted "accept", or, dquoted "reject"]
    s ["For every", keyPair <> ", the", signatureVerificationAlgorithm, "must accept the signature computed by the", signingAlgorithm]

signatureForgeryGameDefinition :: Note
signatureForgeryGameDefinition = de $ do
    lab signatureForgeryGameDefinitionLabel
    s [the, signatureForgeryGame', "between an", adversary, anda, challenger, "is played as follows"]
    enumerate $ do
        item $ s [the, challenger, "uses the", keyGenerator, "to generate a", keyPair, "and sends the", signatureVerificationKey, "to the", adversary]
        item $ s [the, adversary, "can ask arbitrary", messages, "to be signed by the", challenger]
        item $ s [the, adversary, "chooses a", message, anda, signature, "and wins the game if the", signature, "is a valid", signature, "for the", message, "and the", message, "was not queried yet"]

digitalSignatureSecurity :: Note
digitalSignatureSecurity = de $ do
    s ["A", digitalSignatureScheme, "is said to be", dquoted "secure against existential forgery under a chosen-message attack", "if no feasible", adversary, "can win the", signatureForgeryGame, "with a non-negligible", probability]


hashFunctionDefinition :: Note
hashFunctionDefinition = de $ do
    lab hashFunctionDefinitionLabel
    let d = "D"
        r = "R"
    s ["A", hashFunction', "is a", function, m $ fun hshf_ d r, "where", m $ setsize d, "is (much) larger than", m $ setsize r]
    s ["Elements of", m d, "are called", hashes']
    let k = "k"
    s ["Typically", m $ d =: bitss "*", and, m $ r =: bitss k, "for some suitable", m $ natural k]

collisionFindingGameDefinition :: Note
collisionFindingGameDefinition = de $ do
    lab collisionFindingGameDefinitionLabel
    s ["Let", m hshf_, "be a", hashFunction]
    s [the, collisionFindingGame', "between an", adversary, anda, challenger, "is played as follows"]
    enumerate $ do
        let x = "x"
            x' = "x'"
        item $ s [the, adversary, "can obtain the", hash, m $ hsh x, "for any argument", m x, "of their choice"]
        item $ s [the, adversary, "outputs a pair of", messages, m $ tuple x x', "and wins the game if they are different but their", hashes, "are the same"]

collisionResistantDefinition :: Note
collisionResistantDefinition = de $ do
    lab collisionResistantDefinitionLabel
    let c = "c"
        cc = "C"
        hc = hshf_ !: c
    s ["A parametrized family", m $ setcmpr hc (c ∈ cc), "of", hashFunctions, "is called", collisionResistant, "if no feasible", adversary, "can win the", collisionFindingGame, "with a non-negligible", probability, "for a", hashFunction, m hc, "(known to the", adversary <> ") chosen uniformly at random from the family of", hashFunction]
