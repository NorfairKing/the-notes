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
import           Cryptography.SymmetricCryptography.Macro
import           Cryptography.SymmetricCryptography.Terms         hiding
                                                                   (advantage,
                                                                   advantage')
import           Cryptography.SystemAlgebra.AbstractSystems.Macro
import           Cryptography.SystemAlgebra.AbstractSystems.Terms
import           Cryptography.SystemAlgebra.DiscreteSystems.Terms
import           Cryptography.SystemAlgebra.Graph

import           Cryptography.SystemAlgebra.SecureChannels.Macro
import           Cryptography.SystemAlgebra.SecureChannels.Terms

secureChannelsSS :: Note
secureChannelsSS = subsection "Secure Channels" $ do
    todo "move this whole section to after computational problems"
    channelDefinition
    authenticatedChannelDefinition
    secretChannelDefinition
    secureChannelDefinition
    keyChannelDefinition
    distinguisherDefinition
    symmetricCryptoSystemsTransformer
    secureFromAuthenticated
    diffieHellmanDistinguisher

channelDefinition :: Note
channelDefinition = do
    let a = "A"
        b = "B"
        e = "E"
    de $ do
        lab channelDefinitionLabel
        lab communicationChannelDefinitionLabel
        s ["A", communicationChannel', or, channel', m comC, "is a", nS 3, "with", interfaces, "labeled", csa [m a, m b, m e]]
        tikzFig "Communication channel model" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/channelTikZ.tex|]
        let sys = System "Channel" ["A", "B", "E"]
        systemFig 4 sys $ s ["A", communicationChannel, "from the", systemAlgebra, "point of view"]

    nte $ do
        s ["A", communicationChannel, "models the situation in which two", parties, "interact via", messages, "on the", interfaces, csa [m a, m b], "with the possible interference via", m e]
        s ["On an insecure", communicationChannel <> ",", m e, "can read and modify any", message, "going from", m a, to, m b]
        s ["We model the interaction to be one-way and model two-way communication using two channels"]

authenticatedChannelDefinition :: Note
authenticatedChannelDefinition = de $ do
    lab authenticatedChannelDefinitionLabel
    let a = "A"
        b = "B"
        e = "E"
    s ["An", authenticatedChannel', m autC, "is a", communicationChannel, "where", m e, "cannot modify", messages, "going from", m a, to, m b]
    tikzFig "Authenticated Communication Channel" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/autChannelTikZ.tex|]

secretChannelDefinition :: Note
secretChannelDefinition = de $ do
    lab secretChannelDefinitionLabel
    let a = "A"
        b = "B"
        e = "E"
        f = "f"
    s ["A", secretChannel', m secrC, "is a", communicationChannel, "where", m e, "cannot read", messages, "going from", m a, to, m b, "but will get a", function, m f, "of any transmitted", message]
    tikzFig "Secret Communication Channel" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/secrChannelTikZ.tex|]
    s ["Ideally", m f, "is of course the", unitFunction, m unitf_]
    s ["in that case the", secretChannel, "looks as follows"]
    tikzFig "Secret Communication Channel with unit function leak" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/unitSecrChannelTikZ.tex|]

secureChannelDefinition :: Note
secureChannelDefinition = de $ do
    lab secureChannelDefinitionLabel
    let f = "f"
    s ["A", secureChannel', m secuC, "provides both secrecy and authentication but leaks a", function, m f, "of the transmitted", message]
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
    s ["The symbol", m hkeyC, "for parties", m a, and, m b, "denotes that", m a, "knows that at most", m b, "knows the", key, "but", m b, "does not necessarily know who else holds the", key]

distinguisherDefinition :: Note
distinguisherDefinition = de $ do
    let p = "P"
        q = "Q"
    s ["Let", m p, and, m q, "be two", systems]
    s ["A", distinguisher', "is an algorithm that can access a", system, "(one of those two)", "and outputs a bit"]
    s [the, distinguisher <> "'s", advantage', "is defined as the", probability, "that the", distinguisher, "outputs a bit that correctly indicates which of the two", systems, "it has been accessing"]

symmetricCryptoSystemsTransformer :: Note
symmetricCryptoSystemsTransformer = de $ do
    let a = "A"
        b = "B"
    s ["Let", m keyC, "be a", keyChannel, and, m comC, "a", communicationChannel]
    s ["Let", m scs_, "be a", symmetricCryptosystem]
    s ["We define two transformers", m $ encT_ ^: a, and, m $ decT_ ^: b, "that are each", nSs 3, "to encrypt or decrypt, respectively, any passing message with the", key]
    tikzFig "Encryption Transformer" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/encTransformerTikZ.tex|]
    tikzFig "Decryption Transformer" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/decTransformerTikZ.tex|]

secureFromAuthenticated :: Note
secureFromAuthenticated = ex $ do
    s ["Let", m autC, "be a single-use", authenticatedChannel, and, "let", m secuC, "be a", secureChannel, "without deletion that leaks the length"]
    let mesg = "m"
        a = "A"
        b = "B"
        e = "E"
    s ["More specifically, on an input", message, m $ mesg ∈ bitss "*", "at", interface, m a <> ",", m autC, "outputs", m mesg, "at", interfaces, m e, and, m b <> ",", and, m secuC, "outputs the length", m $ len mesg, "at", interface, m e]
    let k = "k"
    s ["Further, let", m keyC, "be a shared secret", keyChannel, "that initially outputs a uniformly random", key, m $ k ∈ bitss kappa, "at", interfaces, m a, and, m b, "(and nothing at", interface, m e <> ")"]

    itemize $ do
        item $ do
            let g_ = "g"
                g = fn g_
                n = "n"
            s ["Let", m $ fun g_ (bitss kappa) (bitss n), "be a", pseudoRandomGenerator]
            let c = "c"
                x = "x"
            s ["Let", texttt "enc", "be the converter that, on input", m $ mesg ∈ msp_, "at its outside interface, computes", m $ x =: g k, "and outputs", m $ c =: mesg `xor` x, "to the receiver"]
            s ["Let", texttt "dec", "be the converter that, on input", m $ c ∈ csp_, "at its outside interface, computes", m $ x =: g k, "and outputs", m $ c `xor` x, "to the receiver"]

            tikzFig "The situation" [] $ raw $ [litFile|src/Cryptography/SystemAlgebra/secureFromAuthenticatedTikZ.tex|]

            s ["We define a simulator", m sigma, "as the", system, "that, on input", m $ len mesg, "at its inside", interface <> ", generates a", ciphertext, m $ c ∈ bitss (len mesg), "uniformly at random and outputs its at its outside", interface]
            newline
            let d = "D"
                rr = "R"
                ss = "S"
                gu = g $ "U" !: kappa
                un = "U" !: n
            s ["Now any", distinguisher, m d, "that can distinguish", m $ rr =: conv encT_ "A" (conv decT_ "B" (listofs [keyC, autC])), "from", m $ ss =: conv sigma "E" (listof secuC), with, advantage, m alpha, "can be used to distinguish", m gu, from, m un]

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
            s ["An", authenticatedChannel, m autC, "where the", interface, m a, "takes an input", m $ mesg ∈ grps_, "and outputs", m mesg, "at", interfaces, m b, and, m e]
        item $ do
            s ["An", authenticatedChannel, m autCB, "with the", interfaces, m a, and, m b, "exchanged"]
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
    let s1 = conv dh a (conv dh b (listofs [autC, autCB]))
        s2 = conv sigma e keyC
    s ["In this setting, any", distinguisher, m d, for, m s1, and, m s2, "has a smaller", advantage, "than any solver for the", decisionalDiffieHellman, "problem"]

    proof $ do
        let a_ = "a"
            b_ = "b"
        s [the, system, m s1, "outputs, for uniformly random", elements, m a_, and, m b_, "of", m $ intmod (ord grps_), "the", elements, m $ g ^ a_, and, m $ g ^ b_, at, interface, m e, and, m $ g ^ (a * b), at, interfaces, m a, and, m b]
        s ["Distinguishing these two precicely corresponds to solving the", decisionalDiffieHellman, "problem for", m grp_]






