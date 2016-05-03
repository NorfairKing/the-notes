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
import           Probability.ConditionalProbability.Macro
import           Probability.ProbabilityMeasure.Macro
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
        keyEncapsulationTransformer
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
    s ["Let", m keyC, "be a", keyChannel, and, m comC_, "a", communicationChannel]
    s ["Let", m scs_, "be a", symmetricCryptosystem]
    s ["We define two transformers", m encT_ , and, m decT_, "that are each", nSs 3, "to encrypt or decrypt, respectively, any passing message with the", key]
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


keyEncapsulationTransformer :: Note
keyEncapsulationTransformer = de $ do
    s ["Let", m kem_, beA, keyEncapsulationMechanism, with, messageSpace, m msp_, publicKeySpace, m pksp_ <> ",", secretKeySpace, m sksp_ <> ", symmetric", keySpace, m ksp_, and, ciphertextSpace, m csp_]
    s ["We define two transformers", m encapT_, and, m decapT_, "that are each", nSs 3, "that works as follows"]
    tikzFig "Encapsulation Transformer" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/encapTransformerTikZ.tex|]
    tikzFig "Decapsulation Transformer" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/decapTransformerTikZ.tex|]
    itemize $ do
        let c = "c"
            k = "k"
        let pk = "p"
            sk = "s"
            kp = tuple pk sk
        item $ do
            s ["First", m decapT_, "samples a", keyPair, m kp, from, m kpdist_]
            s ["It then sends", m pk, "out the top inside", interface, "and keeps", m sk, "for later"]
            s ["Upon receival of a", message, m c, at, "the bottom inside", interface, "it computes", m $ k =: decap c sk, "and outputs", m k, "at its outside", interface, "if it differs from", m undef]
        item $ do
            s [m encapT_ <> ", upon receival of a", message, m p, "on its top inside", interface, "computes", m $ tuple k c =: encap pk, ", sends", m k, "to its outside", interface, and, m c, "to its bottom inside", interface]



unilateralKeyFromFromAuthenticatedAndInsecure :: Note
unilateralKeyFromFromAuthenticatedAndInsecure = thm $ do
    s ["A", unilateralKeyChannel, "can be constructed using a", keyEncapsulationMechanism, "from an", authenticatedChannelWithoutDeletion, anda, channelWithDeletion]
    let aut = autCB pksp_
    let insec = comCwd csp_
    let ukey = ukeyC ksp_
    let pk = "p"
        sk = "s"
    let kp = tuple pk sk
    let c = "c"
        k = "k"
    let c' = c <> "'"
        k' = k <> "'"
    itemize $ do
        item $ s ["Let", m kem_, beA, keyEncapsulationMechanism, with, messageSpace, m msp_, publicKeySpace, m pksp_ <> ",", secretKeySpace, m sksp_ <> ", symmetric", keySpace, m ksp_, and, ciphertextSpace, m csp_]
        item $ s ["Let", encapT_, and, decapT_, "its", converters]
        item $ s ["Let", m aut, "be an", authenticatedChannelWithoutDeletion, for, m pksp_]
        item $ s ["Let", m insec, "be an insecure", channelWithDeletion, for, m csp_]
        item $ s ["Let", m ukey, "be a", unilateralKeyChannel, for, m ksp_]
        item $ do
            let sim = sigma
            s ["let", m sim, "be a", converter, "as follows"]
            s [m sim, "samples a", keyPair, m $ kp ∈ pksp_ ⨯ sksp_, "according to", m kpdist_ <> ",", "computes", m $ tuple c k =: encap pk, and, "outputs", m $ tuple pk c, "at its outside", interface]
            s ["On input", m c', "at its outside", interface, "it outputs, it outputs", m deliverM, "at its inside", interface, "if", m $ c' =: c, and, m $ k' =: decap c' sk, "if", m $ c' `neq` c, and, m $ k' `neq` undef]
    let d = "Dist"
        a = alpha
        ss = "S"
        rr = "R"
        ss_ = conv sigma "E" (listof ukey)
        rr_ = conv encapT_ "A" (conv decapT_ "B" (listofs [aut, insec]))
    s ["For every", distinguisher, m d, with, advantage, m a, "in distinguishing", m $ ss =: ss_, from, m $ rr =: rr_, "there exists an", adversary, with, advantage, m a, "in the", iNDCCA, game, "for the", keyEncapsulationMechanism]

    tikzFig "The situation" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/unilateralKeyFromFromAuthenticatedAndInsecureTikZ.tex|]

    proof $ do
        s ["Let", m d, "be a", distinguisher, for, m rr_, and, m ss_, with, advantage, m a]
        let adv = "Adv"
            a = "A"
            b = "B"
            e = "E"
        itemize $ do
            item $ do
                s ["We construct an", adversary, m adv, "for the", kEM, iNDCCA, game, with, advantage, m alpha]
                s ["In the first stage of the game,", m a, "receives a triple", m $ triple pk c k ∈ (pksp_ ⨯ csp_ ⨯ ksp_)]
                s ["Internally,", m a, "simulates", m d, "internally and gives", m pk, to, m d, at, interface, m e, "simulated as coming from the", authenticatedChannelWithoutDeletion]
                s ["Then it gives", m c, to, m d, at, interface, m e, "as coming from the insecure", channelWithDeletion <> ", and it gives", m k, to, m d, at, interface, m a]
                s ["When it receives", m $ c' ∈ csp_, from, m d, at, interface, m e]
                s ["If", m $ c' =: c, "it hands", m k, to, m d, at, interface, m b]
                s ["If", m (c' `neq` c) <> ",",  m a, "queries the", challenger, "to receive the", secretKey, m k', "corresponding to", m c']
                s ["If", m (k' `neq` undef) <> ",", "the", key, m k', "is then given to", m d, at, interface, m b]
                let b = "b"
                    b' = b <> "'"
                s ["When", m d, "outputs a bit", m b <> ",", m a, "outputs this bit as", m b']
            item $ do
                s ["We show that", m a, "has", advantage, m alpha, "in the", kEM, iNDCCA, game]

                itemize $ do
                    item $ do
                        s ["First suppose that", m $ "b" =: 0, "in the", game]
                        s ["In other words, that", m $ k =: decap c sk, "holds"]
                        s [m adv, "should then output", m 0, "as well"]
                        s ["In this case", csa [m pk, m c, m k], "which", m d, "receives, are exactly distributed as when", m d, "is connected to", m rr]
                        s ["No matter whether", m d, "sends a", ciphertext, m c', "that is equal to", m c, "or not, the distribution of a", m k', "that", m d, "receives", at, interface, m b, "given", csa [m p, m c, m k, m c'], "is equal to the correspondisng distribution of when", m d, "is connected to", m rr]
                        s ["Note that the case where", m $ c' =: c, "holds, follows from the correctness condition of the", kEM]
                        s ["Therefore, in that case,", m d, "will always output that it senses", m rr, "in the case where", m $ "b'" =: 1, and, m $ "b" =: 0]
                        ma $ prob (conv_ d rr =: 1) =: cprob ("b'" =: 1) ("b" =: 0)
                    item $ do
                        s ["Next suppose that", m $ "b" =: 1, "so that", m k, "is independently uniformly random"]
                        s [m adv, "should then output", m 1, "as well"]
                        s ["Then", csa [m p, m c, m k], "are distributed as when", m d, "is connected to", m ss]
                        s ["Also in this case, the distribution of", m k', "given", csa [m p, m c, m k, m c'], "is equal to the corresponding distribution when", m d, "is connected to", m ss]
                        s ["Hence if", m "b", and, m "b'", "are both", m 1, "then", m d, "will output", m 1]
                        ma $ prob (conv_ d ss =: 1) =: cprob ("b'" =: 1) ("b" =: 1)

                s ["We conclude the following"]
                let b = "b"
                    b' = b <> "'"
                aligneqs (2 * (pars $ prob (b' =: b) - 1 / 2))
                    [ 2 * pars ( (1 / 2) * cprob (b' =: 1) (b =: 1) + (1 / 2) * cprob (b' =: 0) (b =: 0) - (1 / 2))
                    , cprob (b' =: 1) (b =: 1) - cprob (b' =: 1) (b =: 0)
                    , prob (conv_ d ss =: 1) - prob (conv_ d rr =: 1)
                    , alpha
                    ]
