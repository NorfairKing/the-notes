module Cryptography.PublicKeyEncryption where

import           Notes                                    hiding (cyclic,
                                                           inverse)

import           Functions.Application.Macro
import           Functions.Basics.Terms
import           Groups.Macro
import           Groups.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Probability.ConditionalProbability.Macro
import           Probability.Independence.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms

import           Cryptography.ComputationalProblems.Terms hiding (advantage,
                                                           advantage')
import           Cryptography.KeyAgreement.Terms
import           Cryptography.SymmetricCryptography.Macro
import           Cryptography.SymmetricCryptography.Terms

import           Cryptography.PublicKeyEncryption.Macro
import           Cryptography.PublicKeyEncryption.Terms

publicKeyEncryptionS :: Note
publicKeyEncryptionS = section "Public key encryption" $ do
    publicKeyEncryptionSchemeDefinition
    iNDCCASecureDefinitionPKEDefinition
    pKEINDCCASecureDefinition
    diffieHellmanPKEDefinition
    elGamalSchemeDefinition
    elGamalSchemeCPASecure
    elGamalSchemeNotCCASecure

publicKeyEncryptionSchemeDefinition :: Note
publicKeyEncryptionSchemeDefinition = de $ do
    lab publicKeyEncryptionSchemeDefinitionLabel
    lab keyGeneratorDefinitionLabel
    s ["Let", m pksp_, "be a so-called", publicKeySpace', and, m sksp_, "a so-called", secretKeySpace']
    s ["A", publicKeyEncryptionScheme', "(" <> pKE' <> ")", "consists of three", functions]
    let pk = "pk"
        sk = "sk"
        mesg = "m"
        c = "c"
        r = "r"
    itemize $ do
        item $ do
            s ["A", keyGenerator', function]
            s ["This is a probabillistic", function, "that generates a", keyPair', m (tuple pk sk) <> ",", "of a", publicKey', m $ pk ∈ pksp_, anda, secretKey', "(" <> privateKey' <> ")", m $ sk ∈ sksp_]
        item $ do
            s ["An", encryptionFunction', m aenc_]
            s ["This is a probabillistic", function, "that takes as inputs a", publicKey, m (pk ∈ pksp_) <> ",", plaintext, m $ sk ∈ sksp_, anda, "fresh randomness value", m $ r ∈ rsp_, "and computes the", ciphertext, m $ c =: aenc mesg pk r ∈ csp_]
        item $ do
            s ["A", decryptionFunction', m adec_]
            s ["This is a deterministic", function, "that takes as inputs a", secretKey, m (sk ∈ sksp_), anda, ciphertext, m $ c ∈ csp_, "and computes the", plaintext, m $ mesg =: adec c sk ∈ msp_]

    s ["... such that for every encryption/decryption", keyPair, "the decryption transformation is the inverse of the encryption transformation"]
    ma $ fa (cs [pk ∈ pksp_, sk ∈ sksp_, mesg ∈ msp_, r ∈ rsp_]) $ adec (aenc mesg pk r) sk =: mesg


iNDCCASecureDefinitionPKEDefinition :: Note
iNDCCASecureDefinitionPKEDefinition = de $ do
    lab iNDCCADefinitionLabel
    lab indistinguishabilityChosenCiphertextAttackDefinitionLabel
    let t = "t"
    s ["A", m t <> "-", message, indistinguishabilityChosenPlaintextAttack', "(" <> iNDCCA' <> ")", "game", "for a", publicKeyEncryptionScheme, "between a", challenger, "and an", adversary, "goes as follows"]
    let b = "b"
        b' = "b'"
    enumerate $ do
        item $ s [the, challenger, "chooses a", secretKey, publicKey, "pair using the", keyGenerator, function, "and sends the", publicKey, "to the adversary"]
        item $ s [the, adversary, "can choose", ciphertexts, "and receive their decryptions under the", secretKey]
        let m0 = "m" !: 0
            m1 = "m" !: 1
            mb = "m" !: b
        item $ s [the, adversary, "chooses two", messages, m m0, and, m m1, "of the same length"]
        let b = "b"
        item $ s [the, challenger, "chooses a uniformly random bit", m b <> ", computes the encryption of", m mb <> ", and returns it to the", adversary]
        item $ s [the, adversary, "can again choose", ciphertexts, "and receive their decryptions as in step 2, but the encryption of", m mb, "is excluded"]
        item $ s [the, adversary, "guesses", m b, "by issuing a guess", m b']
    s [the, advantage', "of the", adversary, "in this game is defined as", m $ 2 * (pars $ prob (b' =: b) - 1 /: 2)]
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
    let zq = intmod q
    itemize $ do
        let a = "A"
            b = "B"
            x = "x"
            y = "y"
            xa = x !: a
            xb = x !: b
            ya = y !: a
            yb = y !: b
            mesg = "m"
        item $ do
            s ["A", keyGenerator, function]
            newline
            s ["Choose", m xb, "uniformly at random from", m zq]
            s [the, secretKey, "is", m xb, "and the", publicKey, "is", m $ yb =: g ^ xb]
        item $ do
            let r = "r"
            s ["An", encryptionFunction]
            newline
            s ["Choose", m xa, "at random from", m zq]
            s [the, ciphertext, "for a", message, m mesg, "is the pair", m $ tuple (g ^ xa) (enc mesg (pars (g ^ xb) ^ xa) r), "where", m r, "is a uniformly random value from the", randomnessSpace, "of", m enc_]
        let c = "c"
        item $ do
            s ["A", decryptionFunction]
            newline
            s ["Given a", ciphertext, "pair", m $ tuple ya c, "the", decryptionFunction, "computes", m $ pars $ ya ^ xb, "to use as the key to decrypt", m $ mesg =: dec c (ya ^ xb)]
    todo "prove that this is in fact a valid PKE"


elGamalSchemeDefinition :: Note
elGamalSchemeDefinition = do
    de $ do
        lab elGamalDefinitionLabel
        s ["A", publicKeyEncryptionScheme, "based on the", diffieHellman, protocol, "where the", symmetricCryptosystem, "is", the, oneTimePad, "is called the", elGamal', publicKeyEncryptionScheme]
    nte $ do
        let q = "q"
        s ["Note that we implicitly use the fact every cyclic group of", finite, order, m q, "is isomorphic to", m $ intmod q]
        refneeded "prove this in the group chapter"

elGamalSchemeCPASecure :: Note
elGamalSchemeCPASecure = thm $ do
    s [the, elGamal, publicKeyEncryptionScheme, "is", iNDCPASecure, "under the", decisionalDiffieHellman, "assumption"]

    proof $ do
        let a = mathcal "A"
        s ["Let", m a, "be an efficient", adversary, "that has", advantage, m alpha, "in the", iNDCPA, "game for public key encryption"]
        let p = "p"
            q = "q"
            r = "r"
            g = "g"
            tr = triple p q r
            x = "x"
            y = "y"
        let d = "D"
        s ["We show that this implies that there is an efficient distinguisher that, given", m (tr ∈ grps_) <> ",", "has", advantage, m $ alpha /: 2, "in distinguishing the case where", csa [m p, m q, m r], "are", independent, "and uniformly distributed over", m grps_, "from the case where", csa [m $ p =: g ^ x, m $ q =: g ^ y, m $ r =: g ^ (x * y)], "holds for", independent, m $ cs [x, y] ∈ intmod "q"]
        newline

        s ["Let", m d, "be the following distinguisher that uses", m a]
        s [m d, "will play the", iNDCPA, "game as the", challenger, "and use", m a, "as the", adversary]
        s ["As the", publicKey <> ",", m d, "sends", m q, "to", m a]
        let mesg = "m"
            m0 = mesg !: 0
            m1 = mesg !: 1
            b = "b"
            mb = mesg !: b
        s ["Whenever", m a, "submits two", messages, m m0, and, m m1 <> ",", m d, "will choose a bit", m b, "uniformly at random and sends", m $ tuple p (mb ** r), to, m a]
        let b' = b <> "'"
        s ["When", m a, "outputs a bit", m b' <> ",", m d, "outputs the bit", m $ b `xor` b', "to distinguish a", diffieHellmanTriple, "from a uniformly random and independent triple"]
        s ["A set bit", m 1, "would indicate the former while an unset bit", m 0, "would indicate the latter"]
        newline
        s ["Now we prove that this distinguisher", m d, "does in fact have", advantage, m $ alpha /: 2, "in solving the", decisionalDiffieHellman, "problem for", m tr]
        itemize $ do
            let ss = "I"
            item $ do
                s ["Denote the situation in which", m tr, "are uniform and", independent, "as", m ss]
                s ["In this situation,",  m $ mb ** r , "is distributed uniformly", ref xorUniformTheoremLabel]
                s ["Moreover, ", csa [m p, m q, m $ mb ** r], "are", independent]
                let v = "v"
                    v1 = v !: 1
                    v2 = v !: 2
                    v3 = v !: 3
                aligneqs (prob $ p =: v1 ∧ q =: v2 ∧ mb ** r =: v3)
                    [ prob $ p =: v1 ∧ q =: v2 ∧ r =: ginv mb ** v3
                    , prob (p =: v1) * prob (q =: v2) * prob (r =: ginv mb ** v3)
                    , prob (p =: v1) * prob (q =: v2) * prob (mb ** r =: v3)
                    ]
                s ["This means that the three values", csa [m p, m q, m $ mb ** r], "that", m a, "sees during the game are uniformly and independently distributed"]
                s ["Since this is true for both possible values of", m b <> ", the ditribution of the output of", m a, "is identical in both cases"]
                newline
                s ["Now observe the following for", m $ ss =: tr, "with", csa [m p, m q, m r], "uniform", and, independent]
                ma $ cprob (fn d tr =: 1 `xor` b) (b =: 0) =: cprob (fn d tr =: 1 `xor` b) (b =: 1)
                s ["This imples the following about", m $ prob (fn d tr =: 1)]
                aligneqs (cprob (fn d tr =: 1) ss)
                    [ (1 /: 2) * cprob (fn d tr =: 1) (b =: 0)
                    + (1 /: 2) * cprob (fn d tr =: 1) (b =: 1)
                    , (1 /: 2) * cprob (fn d tr =: 1) (b =: 0)
                    + (1 /: 2) * (pars $ 1 - cprob (fn d tr =: 0) (b =: 1))
                    , (1 /: 2)
                    ]
                s ["In the third step we used that", m d, "will output", m 1 <> ", given", m tr, with, probability, m $ 1 /: 2, "because", m a, "will output a uniformly random bit given", m tr]
                s ["In other words: if the triple", m tr, "is in fact uniform", and, independent <> ", then", m d, "will output a random and uniform bit"]
            let rr = "J"
            item $ do
                s ["On the other hand, if the triple", m tr, "is a", diffieHellmanTriple, "for uniform", and, independent, m (cs [x, y] ∈ intmod "q") <> "(denote this situation as", m rr <> "), the values", csa [m p, m q, m $ mb ** r], "that", m a, "sees during the game exactly correspond to the values that", m a, "would see in the actual", iNDCPA, "game"]
                aligneqs (cprob (fn d tr =: 0) rr)
                    [ (1 /: 2) * cprob (b' =: 1) (b =: 1)
                    + (1 /: 2) * cprob (b' =: 0) (b =: 0)
                    , (1 /: 2) * cprob (b' =: b) (b =: 0)
                    + (1 /: 2) * cprob (b' =: b) (b =: 1)
                    , prob (b' =: b)
                    ]
                s ["In the second step we rewrite the expression to end up with an expression that will simplify to something involving", m $ prob $ b' =: b]
            item $ do
                s ["Now we can calculate the", advantage, "of", m d, "using the definition"]
                aligneqs (alpha !: d)
                    [ 2 * (abs $ prob (fn d tr =: 1 ∧ ss) + prob (fn d tr =: 0 ∧ rr) - (1 /: 2))
                    , (2 * (abs $ cprob (fn d tr =: 1) ss * prob ss + cprob (fn d tr =: 0) rr * prob rr - (1 /: 2)))
                    , (2 * (abs $ (1 /: 2) * cprob (fn d tr =: 1) ss + (1 /: 2) * cprob (fn d tr =: 0) rr - (1 /: 2)))
                    , (abs $ cprob (fn d tr =: 1) ss + cprob (fn d tr =: 0) rr - 1)
                    , (abs $ (1 /: 2) + prob (b' =: b) - 1)
                    , (abs $ prob (b' =: b) - (1 /: 2))
                    , (abs $ (1 /: 2) * 2 * (pars $ prob (b' =: b) - (1 /: 2)))
                    , (abs $ (1 /: 2) * alpha)
                    , (alpha /: 2)
                    ]
                s ["Overall we obtain that the", advantage, "of", m d, "is equal to", m $ alpha /: 2]




elGamalSchemeNotCCASecure :: Note
elGamalSchemeNotCCASecure = thm $ do
    s [the, elGamal, publicKeyEncryptionScheme, "is not", iNDCCASecure, "under the", decisionalDiffieHellman, "assumption"]
    toprove
