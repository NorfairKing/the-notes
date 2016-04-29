{-# LANGUAGE QuasiQuotes #-}
module Cryptography.MACs where

import           Notes                                    hiding (cyclic,
                                                           inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Logic.PropositionalLogic.Macro
import           Probability.Independence.Terms
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Terms

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

    todo "define the CBC MAC"

    subsection "MAC forgery attacks" $ do
        impersonationAttackDefinition
        substitutionAttackDefinition
        tagVariableDefinition
        uniformTagsDefinition
        uniformTagsImpersonationProbabilityBounded
        independentTagsDefinition
        independentTagsSubstitutionProbabilityBounded
        boundedAttackSuccessExamples


messageAuthenticationCodeDefinition :: Note
messageAuthenticationCodeDefinition = de $ do
    lab messageAuthenticationCodeDefinitionLabel
    lab mACDefinitionLabel
    lab tagSpaceDefinitionLabel
    lab tagDefinitionLabel
    let f = "f"
    s ["A", messageAuthenticationCode', "(" <> mAC' <> ")", "for a", messageSpace, m msp_, ", " <> keySpace, m ksp_, and, tagSpace', m tsp_, "is a", function, m $ fun2 f msp_ ksp_ tsp_]

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
    tikzFig encryptThenMAC [] $ raw $ [litFile|src/Cryptography/MACs/encryptThenMACTikZ.tex|]


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
        tikzFig encryptAndMAC [] $ raw $ [litFile|src/Cryptography/MACs/encryptAndMACTikZ.tex|]
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
    tikzFig mACThenEncrypt [] $ raw $ [litFile|src/Cryptography/MACs/mACThenEncryptTikZ.tex|]


encryptThenMacInsecureForSameKey :: Note
encryptThenMacInsecureForSameKey = thm $ do
    s ["Let", m mfn_, "be a", mAC, "that is", cMASecure, "and let it be used in the", encryptThenMAC, "approach with the", oneTimePad]
    let mesg = "m"
        k = "k"
    s ["If a single", message, m mesg, "is encrypted and tagged with the same", key, m k, "the resulting scheme is no longer", cMASecure, "if an", adversary, "has an encryption oracle"]

    proof $ do
        s ["The following", adversary, "can win the", mACForgery, "game with", probability, m 1]
        itemize $ do
            let c = "c"
            item $ s [the, adversary, "chooses a random", message, m mesg, "and receives its encryption", m c, "from the encryption oracle"]
            item $ s [the, adversary, "wins the", mACForgery, "game by submitting", m $ mfn c k]


unforgableMayLeakPlain :: Note
unforgableMayLeakPlain = thm $ do
    s ["For any ", cMASecure, mAC, ", there exists a", mAC, "that is", cMASecure, "but, when used with any", symmetricCryptosystem, "in an", encryptAndMAC, "fashion, results in an", iNDCPA, "insecure", symmetricCryptosystem]

    proof $ do
        let f_ = mfn_
            f = fn2 f_
        s ["Let", m f_, "be a", mAC, "that is", cMASecure]
        let f'_ = mfn_ <> "'"
        s ["Define the", mAC, m f'_, "as follows"]
        let f'  = fn2 f'_
            mesg = "m"
            k = "k"
        ma $ f' mesg k =: f mesg k ++ mesg
        s ["In other words,", m f'_, "appends the", plaintext, "to the tag of", m f_]
        s [m f'_, "is still", cMASecure, "because if there was a way to forge a tag for", m f'_, "that tag could be reduced in length to obtain a forged tag for", m f_]
        newline

        s ["When", m f'_, "is used in conjunction with any", symmetricCryptosystem, m scs_, "the result of the", encryptAndMAC, "scheme will contain the entire", plaintext, "and can therefore never be", iNDCPASecure]

impersonationAttackDefinition :: Note
impersonationAttackDefinition = de $ do
    lab impersonationAttackDefinitionLabel
    s ["In a", m 0 <> "-" <> message, mACForgery, "game for a", mAC, m mfn_ <> ",", "if an", adversary, "directly submits a", message, "with a valid", tag <> ", this is called an", impersonationAttack']

substitutionAttackDefinition :: Note
substitutionAttackDefinition = de $ do
    lab substitutionAttackDefinitionLabel
    let mesg = "m"
        t = "t"
    s ["In a", m 1 <> "-" <> message, mACForgery, "game for a", mAC, m mfn_ <> ",", "if an", adversary, "obtains a", tag, m t, "for a", message, m mesg, "and submits a differentt", message, "with a valid", tag <> ", this is called an", substitutionAttack']

tagVariableDefinition :: Note
tagVariableDefinition = de $ do
    let f_ = mfn_
        f = fn2 f_
    s ["Let", m f_, "be a", mAC, with, keySpace, m ksp_, "and let the", key, "be uniformly distributed over", m ksp_]
    let mesg = "m"
        kk = "K"
    s ["For a given", message, m mesg <> ",", "we define", m $ f mesg kk, "as the", randomVariable, "for the", tag, "of", m mesg]

uniformTagsDefinition :: Note
uniformTagsDefinition = de $ do
    lab uniformTagsDefinitionLabel
    let f_ = mfn_
        f = fn2 f_
    let mesg = "m"
        kk = "K"
    s ["A", m mAC, m f_, "is said to have", uniformTags', "if, for any", message, m mesg <> ", the", tag, m $ f mesg kk, "is uniformly distributed if the", key, m kk, "is uniformly distributed"]

uniformTagsImpersonationProbabilityBounded :: Note
uniformTagsImpersonationProbabilityBounded = thm $ do
    lab uniformTagsImpersonationProbabilityBoundedTheoremLabel
    let f_ = mfn_
    s ["If a", mAC, m f_, with, tagSpace, m tsp_, "has", uniformTags <> ", then the success", probability, "of an", impersonationAttack, "is bounded by", m $ 1 /: setsize tsp_]
    toprove

independentTagsDefinition :: Note
independentTagsDefinition = de $ do
    lab independentTagsDefinitionLabel
    let f_ = mfn_
        f = fn2 f_
    let mesg = "m"
        m1 = mesg !: 1
        m2 = mesg !: 2
        kk = "K"
    s ["A", mAC, m f_, "is said to have", uniformTags', "if, for any two different", message, m m1, and, m m2 <> ", the", tags, m $ f m1 kk, and, m $ f m2 kk, "are", statisticallyIndependent, "if the", key, m kk, "is uniformly distributed"]

independentTagsSubstitutionProbabilityBounded :: Note
independentTagsSubstitutionProbabilityBounded = thm $ do
    lab independentTagsSubstitutionProbabilityBoundedTheoremLabel
    let f_ = mfn_
    s ["If a", mAC, m f_, with, tagSpace, m tsp_, "has", uniformTags, and, independentTags <> ", then the success", probability, "of a", substitutionAttack, "is bounded by", m $ 1 /: setsize tsp_]

boundedAttackSuccessExamples :: Note
boundedAttackSuccessExamples = do
    ex $ do
        let n = "n"
        s ["Consider the following", mAC, with, messageSpace, m bits <> ",", keySpace, m $ bitss n, and, tagSpace, m $ bitss (n /: 2), "for an even", m n]
        let k = "k"
            k1 = k !: 1
            k2 = k !: 2
            kn = k !: n
            kn2 = k !: (n /: 2)
            kn2p = k !: ((n /: 2) + 1)
            kn2pp = k !: ((n /: 2) + 2)

        ma $ cases $ do
            mfn 0 (tuplelist k1 k2 kn) =: (tuplelist k1 k2 kn2)
            lnbk
            mfn 1 (tuplelist k1 k2 kn) =: (tuplelist kn2p kn2pp kn)

        s ["This", mAC, "has", uniformTags, "and furthermore", independentTags, "because the", tags, "for the", messages, m 0, and, m 1, "are", statisticallyIndependent, "since the bits in the", key, "are", independent]
        s ["Therefore, the probability of any", adversary, "of winning a", m 1 <> "-" <> message, mACForgery, "game is bounded by", m $ 1 /: setsize tsp_ =: 2 ^ (- n /: 2)]

    ex $ do
        let n = "n"
        s ["Consider the following", mAC, with, messageSpace, m terns <> ",", keySpace, m $ bitss n, and, tagSpace, m $ bitss (n /: 2), "for an even", m n]
        let k = "k"
            kk = "K"
            k1 = k !: 1
            k2 = k !: 2
            kn = k !: n
            kn2 = k !: (n /: 2)
            kn2p = k !: ((n /: 2) + 1)
            kn2pp = k !: ((n /: 2) + 2)
        ma $ cases $ do
            mfn 0 (tuplelist k1 k2 kn) =: tuplelist k1 k2 kn2
            lnbk
            mfn 1 (tuplelist k1 k2 kn) =: tuplelist kn2p kn2pp kn
            lnbk
            mfn 2 (tuplelist k1 k2 kn) =: tuplelist (k1 `xor` kn2p) (k2 `xor` kn2pp) (kn2 `xor` kn)
        s [m $ mfn 1 kk, and, m $ mfn 2 kk, "are clearly uniformly distributed (see above)"]
        s ["Because the XOR operation is uniform", ref xorUniformTheoremLabel <> ",", m $ mfn 2 kk, "is also uniformly distributed"]
        s ["This means that this", mAC, "has", uniformTags]
        s ["In the previous example, we already showed that", m $ mfn 0 kk, and, m $ mfn 1 kk, "are", statisticallyIndependent]
        s ["Because", m $ mfn 2 kk, "can be viewed as the", oneTimePad <> "-encryption of", m $ mfn 0 kk, "with", m $ tuplelist kn2p kn2pp kn, "and the", oneTimePad, "produces", statisticallyIndependent, ciphertexts, ref oneTimePadSecurePropertyLabel <> ", and an analogous argument holds for", m (mfn 1 kk) <> ", this", mAC, "also has", independentTags]

    todo "Similarly secure MAC over GF(2 ^ n/2)"









