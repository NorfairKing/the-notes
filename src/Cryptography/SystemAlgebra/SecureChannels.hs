{-# LANGUAGE QuasiQuotes #-}
module Cryptography.SystemAlgebra.SecureChannels where

import           Notes                                            hiding
                                                                   (cyclic)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Groups.Macro
import           Groups.Terms
import           Logic.PropositionalLogic.Macro
import           Probability.ProbabilityMeasure.Terms
import           Sets.Basics.Terms

import           Cryptography.ComputationalProblems.Terms
import           Cryptography.KeyEncapsulation.Macro
import           Cryptography.KeyEncapsulation.Terms
import           Cryptography.PublicKeyEncryption.Macro
import           Cryptography.PublicKeyEncryption.Terms
import           Cryptography.SymmetricCryptography.Macro
import           Cryptography.SymmetricCryptography.Terms         hiding
                                                                   (advantage,
                                                                   advantage')
import           Cryptography.SystemAlgebra.AbstractSystems.Macro
import           Cryptography.SystemAlgebra.AbstractSystems.Terms
import           Cryptography.SystemAlgebra.DiscreteSystems.Terms

import           Cryptography.SystemAlgebra.SecureChannels.Macro
import           Cryptography.SystemAlgebra.SecureChannels.Terms

secureChannelsSS :: Note
secureChannelsSS = subsection "Secure Channels" $ do
    todo "move this whole section to after computational problems"
    subsubsection "Communication Channel" $ do
        channelDefinition
        channelWithoutDeletionDefinition
    subsubsection "Authenticated Channels" $ do
        authenticatedChannelDefinition
        authenticatedChannelWithoutDeletionDefinition
    subsubsection "Secret Channels" $ do
        secretChannelDefinition
        secretChannelWithoutDeletionDefinition
    subsubsection "Secure Channels" $ do
        secureChannelDefinition
        secureChannelWithoutDeletionDefinition
    subsubsection "Key Channels" $ do
        keyChannelDefinition
        unilateralKeyChannelDefinition
    subsubsection "Proving security properties of channels" $ do
        distinguisherDefinition
        symmetricCryptoSystemsTransformer
        secureFromAuthenticatedOTP
        secureFromAuthenticated
        diffieHellmanDistinguisher
        unilateralKeyFromFromAuthenticatedAndInsecure

channelDefinition :: Note
channelDefinition = do
    let a = "A"
        b = "B"
        e = "E"
    de $ do
        lab channelDefinitionLabel
        lab communicationChannelDefinitionLabel
        s ["A", communicationChannel', or, channel', "(with deletion)", m $ comCwd msp_, "with a", messageSpace, m msp_, "is a", nS 3, "with", interfaces, "labeled", csa [m a, m b, m e]]
        tikzFig "Communication channel model" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/channelWDTikZ.tex|]
        s ["It behaves as follows"]
        itemize $ do
            let m_ = "m"
            item $ s ["It can receive a", message, m $ m_ ∈ msp_, at, interface, m a]
            item $ s ["It outputs", m m_, at, interface, m e]
            item $ s ["On input", m deliverM, at, interface, m e, "it outputs", m m_, at, interface, m b]
            let m' = m_ <> "'"
            item $ s ["On input", m $ m' ∈ ksp_, at, interface, m e, "it outputs", m m', at, interface, m b]

    nte $ do
        s ["A", communicationChannel, "models the situation in which a", party, "can send", messages, "over a", channel, "with a party", m b, "with the possible interference and deletion from", m e]
    nte $ do
        s ["Communication channels are considered single-use, we use multiple different", channels, "to model situations in which multiple", messages, "are considered"]
    nte $ do
        -- s ["On an insecure", communicationChannel <> ",", m e, "can read and modify any", message, "going from", m a, to, m b]
        s ["We model the interaction to be one-way and model two-way communication using two different", channels]

channelWithoutDeletionDefinition :: Note
channelWithoutDeletionDefinition = de $ do
    lab channelWithoutDeletionDefinitionLabel
    let a = "A"
        b = "B"
        e = "E"
    s ["A", channelWithoutDeletion, m $ comC msp_, "with a", messageSpace, m msp_, "is a", nS 3, "with", interfaces, "labeled", csa [m a, m b, m e]]
    tikzFig "Communication channel without deleteion" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/channelTikZ.tex|]
    s ["It models the fact that", m a, "can send a", message, to, m b, "with the guarantee that it cannot be deleted, but", m e, "can still change the", message, "before it arrives at", m b]
    todo "does this need more formalizing?"

authenticatedChannelDefinition :: Note
authenticatedChannelDefinition = de $ do
    lab authenticatedChannelDefinitionLabel
    let a = "A"
        b = "B"
        e = "E"
    s ["An", authenticatedChannel', m $ autCwd msp_, "with a", messageSpace, m msp_, "is a", communicationChannel, "where", m e, "cannot modify the", message, "going from", m a, to, m b]
    tikzFig "Authenticated Communication Channel with deletion" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/autChannelWDTikZ.tex|]
    s ["It behaves as follows"]
    itemize $ do
        let m_ = "m"
        item $ s ["It can receive a", message, m $ m_ ∈ msp_, at, interface, m a]
        item $ s ["It outputs", m m_, at, interface, m e]
        item $ s ["On input", m deliverM, at, interface, m e, "it outputs", m m_, at, interface, m b]

authenticatedChannelWithoutDeletionDefinition :: Note
authenticatedChannelWithoutDeletionDefinition = de $ do
    lab authenticatedChannelWithoutDeletionDefinitionLabel
    let a = "A"
        b = "B"
        e = "E"
    s ["An", authenticatedChannelWithoutDeletion', m $ autC msp_, "with a", messageSpace, m msp_, "is a", communicationChannelWithoutDeletion, "where", m e, "cannot modify the", message, "going from", m a, to, m b]
    tikzFig "Authenticated Communication Channel without deletion" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/autChannelTikZ.tex|]

secretChannelDefinition :: Note
secretChannelDefinition = de $ do
    lab secretChannelDefinitionLabel
    let a = "A"
        b = "B"
        e = "E"
        f = "f"
    s ["A", secretChannel', m $ secrCwd msp_, "with a", messageSpace, m msp_, "is a", communicationChannel, "where", m e, "cannot read", messages, "going from", m a, to, m b, "but will get a", function, m f, "of any transmitted", message]
    tikzFig "Secret Communication Channel" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/secrChannelWDTikZ.tex|]
    s ["Ideally", m f, "is of course the", unitFunction, m unitf_]
    s ["in that case the", secretChannel, "looks as follows"]
    tikzFig "Secret Communication Channel with unit function leak" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/unitSecrChannelWDTikZ.tex|]
    itemize $ do
        let m_ = "m"
        item $ s ["It can receive a", message, m $ m_ ∈ msp_, at, interface, m a]
        item $ s ["It then outputs", m $ fn f m_, at, interface, m e]
        item $ s ["On input", m deliverM, at, interface, m e, "it outputs", m m_, at, interface, m b]
        let m' = m_ <> "'"
        item $ s ["On input", m $ m' ∈ msp_, at, interface, m e, "it outputs", m m', at, interface, m b]

secretChannelWithoutDeletionDefinition :: Note
secretChannelWithoutDeletionDefinition = de $ do
    lab secretChannelWithoutDeletionDefinitionLabel
    let a = "A"
        b = "B"
        e = "E"
        f = "f"
    s ["A", secretChannel', m $ secrC msp_, "with a", messageSpace, m msp_, "is a", communicationChannelWithoutDeletion, "where", m e, "cannot read", messages, "going from", m a, to, m b, "but will get a", function, m f, "of any transmitted", message]
    tikzFig "Secret Communication Channel" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/secrChannelTikZ.tex|]
    s ["Ideally", m f, "is of course the", unitFunction, m unitf_]
    s ["in that case the", secretChannelWithoutDeletion, "looks as follows"]
    tikzFig "Secret Communication Channel with unit function leak" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/unitSecrChannelTikZ.tex|]

secureChannelDefinition :: Note
secureChannelDefinition = de $ do
    lab secureChannelDefinitionLabel
    let a = "A"
        b = "B"
        e = "E"
        f = "f"
    s ["A", secureChannel', m $ secuCwd msp_, "with a", messageSpace, m msp_, "provides both secrecy and authentication but leaks a", function, m f, "of the transmitted", message]
    tikzFig "Secure Channel" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/secuChannelWDTikZ.tex|]
    s ["Ideally", m f, "is of course the", unitFunction, m unitf_]
    s ["in that case the", secureChannel, "looks as follows"]
    tikzFig "Secure Channel" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/unitSecuChannelWDTikZ.tex|]
    itemize $ do
        let m_ = "m"
        item $ s ["It can receive a", message, m $ m_ ∈ msp_, at, interface, m a]
        item $ s ["It outputs", m $ fn f m_, at, interface, m e]
        item $ s ["On input", m deliverM, at, interface, m e, "it outputs", m m_, at, interface, m b]

secureChannelWithoutDeletionDefinition :: Note
secureChannelWithoutDeletionDefinition = de $ do
    lab secureChannelWithoutDeletionDefinitionLabel
    let f = "f"
    s ["A", secureChannelWithoutDeletion', m $ secuC msp_, "with a", messageSpace, m msp_, "provides both secrecy and authentication but leaks a", function, m f, "of the transmitted", message]
    tikzFig "Secure Channel" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/secuChannelTikZ.tex|]
    s ["Ideally", m f, "is of course the", unitFunction, m unitf_]
    s ["in that case the", secureChannel, "looks as follows"]
    tikzFig "Secure Channel" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/unitSecuChannelTikZ.tex|]

keyChannelDefinition :: Note
keyChannelDefinition = de $ do
    lab keyChannelDefinitionLabel
    let a = "A"
        b = "B"
        e = "E"
    s ["A", keyChannel', m keyC, "is a", communicationChannel, "that can generate", keys, "from some", keySpace, "and share them with", m a, and, m b, "but where", m e, "cannot read or modify those", keys]
    tikzFig "Key Channel" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/keyChannelTikZ.tex|]

unilateralKeyChannelDefinition :: Note
unilateralKeyChannelDefinition = de $ do
    lab unilateralKeyChannelDefinitionLabel
    let a = "A"
        b = "B"
        e = "E"
    s ["Let", m ksp_, "be a", keySpace]
    s ["A", unilateralKeyChannel', m ukeyC_, "is a", communicationChannel, "that functions as follows"]
    tikzFig "Key Channel" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/ukeyChannelTikZ.tex|]
    itemize $ do
        let k = "k"
        item $ s ["First it chooses", m $ k ∈ ksp_, "uniformly at random"]
        item $ s ["It outputs", m k, at, interface, m a]
        item $ s ["On input", m deliverM, at, interface, m e, "it outputs", m k, at, interface, m b]
        let k' = k <> "'"
        item $ s ["On input", m $ k' ∈ ksp_, at, interface, m e, "it outputs", m k', at, interface, m b]

distinguisherDefinition :: Note
distinguisherDefinition = de $ do
    let p = "P"
        q = "Q"
    s ["Let", m p, and, m q, "be two", systems]
    s ["A", distinguisher', "is an algorithm that can access a", system, "(one of those two)", "and outputs a bit"]
    s [the, distinguisher <> "'s", advantage', "is defined as the", probability, "that the", distinguisher, "outputs a bit that correctly indicates which of the two", systems, "it has been accessing"]
    todo "move this to the right place?"

symmetricCryptoSystemsTransformer :: Note
symmetricCryptoSystemsTransformer = de $ do
    let a = "A"
        b = "B"
    s ["Let", m keyC, "be a", keyChannel, and, m comC_, "a", communicationChannel]
    s ["Let", m scs_, "be a", symmetricCryptosystem]
    s ["We define two transformers", m $ encT_ ^: a, and, m $ decT_ ^: b, "that are each", nSs 3, "to encrypt or decrypt, respectively, any passing message with the", key]
    tikzFig "Encryption Transformer" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/encTransformerTikZ.tex|]
    tikzFig "Decryption Transformer" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/decTransformerTikZ.tex|]

secureFromAuthenticatedOTP :: Note
secureFromAuthenticatedOTP = ex $ do
    s ["Let", m autC_, "be a single-use", authenticatedChannel, and, "let", m secuC_, "be a", secureChannel, "without deletion that leaks the length"]
    let mesg = "m"
        a = "A"
        b = "B"
        e = "E"
    s ["More specifically, on an input", message, m $ mesg ∈ bitss "*", "at", interface, m a <> ",", m autC_, "outputs", m mesg, "at", interfaces, m e, and, m b <> ",", and, m secuC_, "outputs the length", m $ len mesg, "at", interface, m e]
    let k = "k"
    s ["Further, let", m keyC, "be a shared secret", keyChannel, "that initially outputs a uniformly random", key, m $ k ∈ bitss kappa, "at", interfaces, m a, and, m b, "(and nothing at", interface, m e <> ")"]

    let g_ = "g"
        g = fn g_
        n = "n"
    let c = "c"
        x = "x"
    s ["Let", m $ fun g_ (bitss kappa) (bitss n), "be a", pseudoRandomGenerator]
    s ["Let", texttt "enc", "be the converter that, on input", m $ mesg ∈ msp_, "at its outside interface, computes", m $ x =: g k, "and outputs", m $ c =: mesg `xor` x, "to the receiver"]
    s ["Let", texttt "dec", "be the converter that, on input", m $ c ∈ csp_, "at its outside interface, computes", m $ x =: g k, "and outputs", m $ c `xor` x, "to the receiver"]

    tikzFig "The situation" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/secureFromAuthenticatedOTPTikZ.tex|]

    s ["We define a simulator", m sigma, "as the", system, "that, on input", m $ len mesg, "at its inside", interface <> ", generates a", ciphertext, m $ c ∈ bitss (len mesg), "uniformly at random and outputs its at its outside", interface]
    newline
    let d = "D"
        rr = "R"
        ss = "S"
        gu = g $ "U" !: kappa
        un = "U" !: n
    s ["Now any", distinguisher, m d, "that can distinguish", m $ rr =: conv encT_ "A" (conv decT_ "B" (listofs [keyC, autC_])), "from", m $ ss =: conv sigma "E" (listof secuC_), with, advantage, m alpha, "can be used to distinguish", m gu, from, m un]

    proof $ do
        let d' = d <> "'"
        s ["Let", m d, "be such a", distinguisher, with, advantage, m alpha, "we define a", distinguisher, m d', "that distinguishes", m gu, from, m un, "as follows"]
        s ["Initially,", m d', "expects a", key, m $ k ∈ bitss n, "as input"]
        s ["It then decides whether", m k, "came from the", pseudoRandomGenerator, m g_, "or was drawn from a real uniform random distribution on", m $ bitss n, "as follows"]
        s [m d', "chooses a message", m $ mesg ∈ bitss n, "uniformly at random and feeds it to", m d, "along with the expected outputs", m $ c =: mesg `xor` k, "at", interface, m e, and, m mesg, "at", interface, m b]
        s [m d, "will output a bit and", m d', "will output the same bit"]
        newline
        s ["Note that if", m k, "is generated by", m gu <> ", then", m c, "is distributed as in", m rr, "and if", m k, "is a uniformly random key, then", m c, "is distributed as the", ciphertexts, "in", m ss]
        s ["Hence, the advantage of", m d', "equals the advantage of", m d]

secureFromAuthenticated :: Note
secureFromAuthenticated = thm $ do
    s ["Let", m autC_, "be a single-use", authenticatedChannel, and, "let", m secuC_, "be a", secureChannel, "without deletion that leaks the length"]
    let mesg = "m"
        a = "A"
        b = "B"
        e = "E"
    let g_ = "g"
        n = "n"
    s ["Let", m $ fun g_ (bitss kappa) (bitss n), "be a", pseudoRandomGenerator]
    let c = "c"
    s ["More specifically, on an input", message, m $ mesg ∈ bitss "*", "at", interface, m a <> ",", m autC_, "outputs", m mesg, "at", interfaces, m e, and, m b <> ",", and, m secuC_, "outputs the length", m $ len mesg, "at", interface, m e]
    let k = "k"
    s ["Further, let", m keyC, "be a shared secret", keyChannel, "that initially outputs a uniformly random", key, m $ k ∈ bitss kappa, "at", interfaces, m a, and, m b, "(and nothing at", interface, m e <> ")"]
    let scs = tuple enc_ dec_
    s ["Let", m scs, "be a", symmetricCryptosystem, and, encT_, and, decT_, "its encryption and decryption transformers"]

    tikzFig "The situation" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/secureFromAuthenticatedTikZ.tex|]

    s ["We define a simulator", m sigma, "as the", system, "that, on input", m $ len mesg, "at its inside", interface <> ", generates a", ciphertext, m $ c ∈ bitss (len mesg), "uniformly at random and outputs its at its outside", interface]
    newline
    let rr = "R"
        ss = "S"
        ss_ = conv sigma "E" (listof secuC_)
        rr_ = conv encT_ "A" (conv decT_ "B" (listofs [keyC, autC_]))
    s ["This construction of", m $ ss =: ss_, "from", m $ rr =: rr_, "can be achieved if and only if", m scs, is, m 0 <> "-" <> message, iNDCPA, "secure"]

    proof $ do
        s ["We prove each direction separately"]
        itemize $ do
            item $ do
                s ["If", m scs, "is", m 0 <> "-" <> message, iNDCPA, "secure", "then any", distinguisher, "that can distinguish", m ss, from, m rr, "can be used to build a", challenger, "that can win the", m 0 <> "-" <> message, iNDCPA, "game", for, m scs]
                clarify "with which advantages?"
            item $ do
                s ["For every simulator", m sigma, "and every feasible", m 0 <> "-" <> message, challenger, with, advantage, m alpha, "there is a feasible", distinguisher, with, advantage, m $ alpha / 2, "in distinguishing", m ss, from, m rr]
    toprove


diffieHellmanDistinguisher :: Note
diffieHellmanDistinguisher = thm $ do
    let g = "g"
    s ["Let", m grp_, "be a", finite, cyclic, group, "and let", m $ g ∈ grps_, beA, generator, "of", m grp_]
    s ["We assume that", m grp_, and, m g, "are publicly known and define all the following", systems, and, protocols, "relative to them"]
    s ["Consider the following two", systems]
    let a = "A"
        b = "B"
        e = "E"
    let dh = "DH"
    let x = "x"
    let y = "y"
        g1 = g !: 1
        g2 = g !: 2
    itemize $ do
        item $ do
            let mesg = "m"
            s ["An", authenticatedChannel, m autC_, "where the", interface, m a, "takes an input", m $ mesg ∈ grps_, "and outputs", m mesg, "at", interfaces, m b, and, m e]
        item $ do
            s ["An", authenticatedChannel, m autCB_, "with the", interfaces, m a, and, m b, "exchanged"]
        item $ do
            s [the, protocol, system, m dh, "as a", converter]
            s ["This", system, "first chooses a", group, element, m x, "uniformly at random and outputs it at its inside", interface]
            s ["Whenever it receives a", group, element, m y, "at its inside", interface, "it outputs", m $ y ^ x, "at its outside", interface]
        item $ do
            let k = "k"
            s ["A", keyChannel, m keyC, "that chooses", m $ k ∈ grps_, "uniformly at random and outputs it at only at", interfaces, m a, and, m b]
        item $ do
            s ["A simulator", m sigma, "as a", converter, "of the", m e, interface, "that outputs two uniformly random", group, elements, m g1, and, m g2, "at its outside interface"]
    tikzFig "The situation" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/diffieHellmanSituationTikZ.tex|]
    let d = "D"
    let s1 = conv dh a (conv dh b (listofs [autC_, autCB_]))
        s2 = conv sigma e keyC
    s ["In this setting, any", distinguisher, m d, for, m s1, and, m s2, "has a smaller", advantage, "than any solver for the", decisionalDiffieHellman, "problem"]

    proof $ do
        let a_ = "a"
            b_ = "b"
        s [the, system, m s1, "outputs, for uniformly random", elements, m a_, and, m b_, "of", m $ intmod (ord grps_), "the", elements, m $ g ^ a_, and, m $ g ^ b_, at, interface, m e, and, m $ g ^ (a * b), at, interfaces, m a, and, m b]
        s ["Distinguishing these two precicely corresponds to solving the", decisionalDiffieHellman, "problem for", m grp_]




unilateralKeyFromFromAuthenticatedAndInsecure :: Note
unilateralKeyFromFromAuthenticatedAndInsecure = thm $ do
    s ["A", unilateralKeyChannel, "can be constructed using a", keyEncapsulationMechanism, "from an", authenticatedChannelWithoutDeletion, anda, channelWithDeletion]
    let aut = autCB pksp_
    let insec = comCwd csp_
    let ukey = ukeyC ksp_
    itemize $ do
        item $ s ["Let", m kem_, beA, keyEncapsulationMechanism, with, messageSpace, m msp_, publicKeySpace, m pksp_ <> ",", secretKeySpace, m sksp_ <> ", symmetric", keySpace, m ksp_, and, ciphertextSpace, m csp_]
        item $ s ["Let", kemEncT_, and, kemDecT_, "its", converters]
        item $ s ["Let", m aut, "be an", authenticatedChannelWithoutDeletion, for, m pksp_]
        item $ s ["Let", m insec, "be an insecure", channelWithDeletion, for, m csp_]
        item $ s ["Let", m ukey, "be a", unilateralKeyChannel, for, m ksp_]
        item $ do
            let sim = sigma
            s ["let", m sim, "be a", converter, "as follows"]
            let pk = "p"
                sk = "s"
            let kp = tuple pk sk
            let c = "c"
                k = "k"
            s [m sim, "samples a", keyPair, m $ kp ∈ pksp_ ⨯ sksp_, "according to", m kpdist_ <> ",", "computes", m $ tuple c k =: encap pk, and, "outputs", m $ tuple pk c, "at its outside", interface]
    let d = "Dist"
        a = alpha
        ss = "S"
        rr = "R"
        ss_ = conv sigma "E" (listof ukey)
        rr_ = conv kemEncT_ "A" (conv kemDecT_ "B" (listofs [aut, insec]))
    s ["For every", distinguisher, m d, with, advantage, m a, "in distinguishing", m $ ss =: ss_, from, m $ rr =: rr_, "there exists an", adversary, with, advantage, m a, "in the", iNDCCA, game, "for the", keyEncapsulationMechanism]

    toprove

