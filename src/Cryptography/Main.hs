module Cryptography.Main where

import           Notes                                    hiding (cyclic,
                                                           inverse, sign)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Inverse.Terms
import           Functions.Jections.Terms
import           Groups.Macro
import           Groups.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           NumberTheory.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Terms
import           Relations.Orders.Macro
import           Sets.Basics.Terms

import           Cryptography.ComputationalProblems
import           Cryptography.ComputationalProblems.Terms hiding (advantage)
import           Cryptography.KeyAgreement
import           Cryptography.KeyEncapsulation
import           Cryptography.Macro
import           Cryptography.MACs
import           Cryptography.PublicKeyEncryption
import           Cryptography.PublicKeyEncryption.Terms
import           Cryptography.SymmetricCryptography
import           Cryptography.SymmetricCryptography.Macro
import           Cryptography.SymmetricCryptography.Terms
import           Cryptography.SystemAlgebra
import           Cryptography.Terms

cryptography :: Note
cryptography = chapter "Cryptography" $ do
    symmetricCryptographyS
    mACS
    keyAgreementS
    publicKeyEncryptionS

    section "Trapdoor one-way permutations" $ do
        trapdoorOneWayPermutationDefinition
        tWOPInversionGame
        ethRootComputation
        rSATWOPDefinition
        tWOPAsPKE
        rsaPKEExample
        rsaSmallEInsecure
        rsaSmallEInsecure2
        totientToFactorisation
        rsaAsHardAsLSB

    section "Digital signatures" $ do
        digitalSignatureDefinition
        signatureForgeryGameDefinition
        digitalSignatureSecurity
        lamportOneTimeSignatureSchemeDefinition
        lamportSecureIfOneWayFunction

    keyEncapsulationS

    section "Hash functions" $ do
        hashFunctionDefinition
        collisionFindingGameDefinition
        collisionResistantDefinition

    systemAlgebraS
    computationalProblemsS

    cryptoRefs

trapdoorOneWayPermutationDefinition :: Note
trapdoorOneWayPermutationDefinition = de $ do
    lab trapdoorOneWayPermutationDefinitionLabel
    lab tWOPDefinitionLabel
    lab trapdoorGeneratorDefinitionLabel
    lab trapdoorFunctionDefinitionLabel
    lab trapdoorDefinitionLabel
    let x = mathcal "X"
        y = mathcal "Y"
    let f_ = "F"
        d_ = "D"
    s ["A", trapdoorOneWayPermutation', "(" <> tWOP <> ")", "is and efficient probabillistic algorithm, the", trapdoorGenerator', "which generates descriptions of two", algorithms, m f_, and, m d_, "and two", sets, m x, and, m y]
    let g_ = "g"
        g = fn g_
    itemize $ do
        item $ do
            let ff = "f"
            s ["An algorithm", m f_, "computing an", injective, function, m $ fun ff x y]
            s ["Typically,", m f_, "is described by a short parameter called the", publicKey, "which also defines", m x, and,m y]
            s [m ff, "is called the", trapdoorFunction']
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
        s ["Let", m $ int e, "be given exponent", relativelyPrime_, "to", m gs]
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
    itemize $ do
        let f = "f"
            g = "g"
            x = "x"
        let z = int0mod n
        item $ do
            s [the, trapdoorGenerator, "chooses two", primes, m p, and, m q, "computes", m $ n =: p * q, "and chooses", m e, "such that", m e, "is", relativelyPrime_, "to", m $ etot n]
            s [the, publicKey, "is the pair", m $ tuple n e]
            s ["It then computes the", trapdoor, m $ d =: e ^ (-1) `mod` etot n]
            let x = mathcal "X"
                y = mathcal "Y"
            s ["It outputs", m $ x =: y =: z, "as the relevant", sets]
        item $ do
            s [m f, "is defined as follows"]
            ma $ func f z z x $ x ^ e
        item $ do
            s [m g, "is defined as follows"]
            ma $ func g z z x $ x ^ d

    todo "prove that the trapdoor allows for the inversion of the trapdoor function"
    todo "prove that this is in fact secure"


tWOPAsPKE :: Note
tWOPAsPKE = de $ do
    s ["Given a", trapdoorOneWayPermutation <> ", we can construct a", publicKeyEncryptionScheme, "as follows"]
    s ["Let the domain of the", trapdoorOneWayPermutation, "be the", messageSpace]
    let f_ = "F"
        d_ = "D"
    s ["Let encryption be the application of the", trapdoorOneWayPermutation <> ", where the", publicKey, "is the description of the algorithm", m f_, "and the", secretKey, "the description of the algorithm", m d_]

rsaPKEExample :: Note
rsaPKEExample = ex $ do
    s ["In this example we will show how we can use the", rSA, trapdoorOneWayPermutation, "to build a", publicKeyEncryptionScheme]
    let n = "n"
    let p = "p"
        q = "q"
        e = "e"
        d = "d"
    let mesg = "m"
        c = "c"
    itemize $ do
        item $ do
            s [the, keyGenerator, function, "generates two primes", m p, and, m q, "and computes", m $ n =: p * q, "as well as", m $ etot n =: (p - 1) * (q - 1), "and selects an", m $ e ∈ integers, "that is relatively prime to", m $ etot n, "to compute", m $ d =: ginv e `mod` etot n]
            itemize $ do
                item $ s [the, publicKey, "is then", m $ tuple n e]
                item $ s [the, privateKey, "is", m d]
        item $ do
            s [the, encryptionFunction, "computes the", ciphertext, m $ c =: mesg ^ e `mod` n, "for a given", message, m mesg]
        item $ do
            s [the, decryptionFunction, "computes the original", message, m $ mesg =: c ^ d `mod` n, "for a given", ciphertext, m c]
    s ["This is in fact a valid", publicKeyEncryptionScheme]
    proof $ do
        s ["Let", m $ cs [p, q] ∈ integers, "be arbitrary and let", m $ mesg ∈ intmod n, "be an arbitrary", message]
        ma $ (pars $ mesg ^ d `mod` n) ^ e `mod` n
          =: (pars $ mesg ^ (ginv e `mod` etot n) `mod` n) ^ e `mod` n
          =: mesg ^ ((pars $ ginv e `mod` etot n) * e) `mod` n
          =: mesg
    why_ "Don't these 'mod n' things pose a problem"
    s ["Note that the", messageSpace, m $ intmod n, "is only decided uppon during the key generation phase"]

rsaSmallEInsecure :: Note
rsaSmallEInsecure = thm $ do
    let e = "e"
        n = "n"
        mesg = "m"
        c = "c"
    s ["When a small", m e, "is selected in the", rSA, publicKeyEncryptionScheme <> ", any", message, "from a considerable subspace of the", messageSpace, "can be efficiently recovered"]
    proof $ do
        let m0 = msp_ !: 0
        s ["For a small", m $ e ∈ intmod n, ", the subspace", m $ m0 =: setcmpr (mesg ∈ naturals) (mesg ^ e < n), "is considerably large (or at least non-negligible and increasing in size for increasing", m n <> ")"]
        s ["For any", message, m (mesg ∈ m0) <> ",", "the corresponding ciphertext equals", m $ c =: mesg ^ e `mod` n =: mesg ^ e]
        s ["In other words, ", m $ mesg ^ e, "is not reduced modulo", m n]
        s ["This means that an", adversary, "can efficiently compute", m $ c ^ (1 /: e), "over the integers and recover", m mesg, "entirely"]

rsaSmallEInsecure2 :: Note
rsaSmallEInsecure2 = thm $ do
    let e = "e"
        n = "n"
        mesg = "m"
        c = "c"
        i = "i"
    s ["When a small", m e, "is selected in the", rSA, publicKeyEncryptionScheme <> ", any", message, "can be efficiently recovered as long as it is send to at least", m e, "different", parties, "who all use the same", m e]
    proof $ do
        let n1 = n !: 1
            n2 = n !: 2
            ni = n !: i
            ne = n !: e
        s ["In this scenario the", m e, parties, "have different moduli", m $ list n1 n2 ne]
        let c1 = c !: 1
            c2 = c !: 2
            ce = c !: e
        s ["Let", m $ list c1 c2 ce, "be the", ciphertexts, "that are sent to these", parties]
        ma $ centeredBelowEachOther
            [ c1 =: mesg ^ e `mod` n1
            , c2 =: mesg ^ e `mod` n2
            , vdots
            , ce =: mesg ^ e `mod` ne
            ]
        s ["Using the", chineseRemainderTheorem_, "we can efficiently compute", m c, "as follows"]
        ma $ c =: mesg ^ e `mod` (prodcmpr (i =: 1) e ni)
        s ["Because", m mesg, "is smaller than every", m ni <> ", it follows that", m $ mesg ^ e < (prodcmpr (i =: 1) e ni), "holds"]
        s ["In other words, ", m c, "is not reduced modulo", m (prodcmpr (i =: 1) e ni)]
        s ["This means that an adversary can recover", m mesg, "entirely by computing the", m e <> "-th root of", m c, "in", m integers]

totientToFactorisation :: Note
totientToFactorisation = thm $ do
    let n = "n"
        p = "p"
        q = "q"
    s ["Let", m n, "be a product of two", primes, m p, and, m q]
    s ["Given", m n, and, m $ etot n, "we can efficiently compute", m p, and, m q]
    proof $ do
        s ["Because", m p, and, m q, are, primes <> ",", m $ etot n =: (pars $ p - 1) * (pars $ q - 1), "must hold"]
        why
        s ["Now observe the following"]
        ma $ p =: n - q + 1 - etot n
        ma $ n =: n * q - q ^ 2 + q - etot n * q
        s ["Since", m n, and, m $ etot n, "are known, we can solve this quadratic system efficiently"]

rsaAsHardAsLSB :: Note
rsaAsHardAsLSB = do
    thm $ do
        let algo = "A"
            a = fn algo
            k = "k"
            n = "n"
            e = "e"
            c = "c"
            mesg = "m"
        s ["In the", rSA, publicKeyEncryptionScheme, "any efficient algorithm", m algo, "which, for a given", csa [m k <> "-bit RSA-modulus" <> m n, "exponent " <> m e, ciphertext <> " " <> m c], "computes the", leastSignificantBit, "of the corresponding plaintext", m mesg <> ", can be used to build an efficient algorithm which, for a given", ciphertext, m c, "computes the entire corresponding", plaintext, m mesg, "by calling algorithm", m algo, m k, "times as a subroutine"]
        footnote $ s ["By", dquoted leastSignificantBit, "we mean", m $ mesg `mod` 2]
        todo "what does this mean in terms of reductions?"

        proof $ do
            s ["Let", m algo, "be an efficient algorithm which, for a given", csa [m k <> "-bit RSA-modulus" <> m n, "exponent " <> m e, ciphertext <> " " <> m (c =: mesg ^ e)], "computes the", leastSignificantBit, "of the corresponding plaintext", m mesg]
            let algo' = "A'"
            s ["This algorithm", m algo, "can be exploited as follows to build an algorithm", m algo', "that computes the entire corresponding", plaintext]

            itemize $ do
                let t = "t"
                item $ do
                    s ["Note first that one can easily compute", m $ (pars $ (2 ^ t) * mesg) ^ e `mod` n]
                    aligneqs ((pars $ (2 ^ t) * mesg) ^ e `mod` n)
                      [ (2 ^ (t * e) * mesg ^ e `mod` n)
                      , (2 ^ (t * e) * c `mod` n)
                      ]
                    why
                let u = "u"
                item $ do
                    s ["Let", m mesg, "be a", message, "such that", m $ mesg < (n / (2 ^ t)), "holds", "for any", m $ t ∈ naturals]
                    s ["Note that this means that", m $ (2 ^ t) * mesg < n, "holds, which implies that", m $ (2 ^ t) * mesg, "is not reduced modulo", m n]
                    s ["For that same", m mesg <> ",", m $ mesg + n / (2 ^ t), "is reduced exactly once modulo", m n, "(" <>(m $ n < (2 ^ t) * mesg + n < 2 * n) <> ")"]
                    s ["Similarly,", m $ mesg + (u * n) / (2 ^ t), "is reduced exactly", m u, "times modulo", m n, "(" <>(m $ (u - 1) * n < (2 ^ t) * mesg + u * n < u * n) <> ")"]
                item $ do
                    s ["Because", m n, "is odd (it's the product of two large primes, yes, larger than", m 2 <> ")", "we can reason about the size of", m mesg, "as follows"]
                    ma $ (a (2 ^ e * c) =: 0) ⇔ (mesg < (n / 2))
                    ma $ (a (4 ^ e * c) =: 0) ⇔ cases (do
                            (0 < mesg < (n / 4))
                            lnbk
                            text $ " " <> or
                            lnbk
                            ((n / 2) < mesg < (3 * n / 4))
                        )
                    ma $ (a (2 ^ (t * e) * c) =: 0) ⇔ ((u / (2 ^ t)) < mesg < ((u + 1) / (2 ^ t))) <> (text $ " with " <> m u <> " even")
                    s ["Concretely, this means that we can find the", m t <> "-th", leastSignificantBit, "of", m mesg, "be querying", m algo, with, m $ 2 ^ (t * e) * c, "and looking at the output"]
                    ma $ a (2 ^ (e * t) * c) =: lsb (roundd $ 2 ^ (e * t) * (mesg / n))
                item $ do
                    s ["Putting all of this information together, we can find", m mesg, "entirely by querying", m algo, m k, "times with input", m $ setcmpr (2 ^ (t * e)) (t ∈ setlist 1 2 t), "respectively"]
    nte $ do
        let k = "k"
        s ["In fact, a stronger theorem can be proven: An algorithm which computes any binary function of the least", m $ log k, "bits of the", plaintext, "with probability non-negligibly greater than", m $ 1 / 2, "of being correct, can be used to compute the entire", plaintext]
        refneeded "to the paper where this is proven"






digitalSignatureDefinition :: Note
digitalSignatureDefinition = de $ do
    lab digitalSignatureSchemeDefinitionLabel
    lab dSSDefinitionLabel
    lab signingKeyDefinitionLabel
    lab signatureVerificationKeyDefinitionLabel
    lab signingAlgorithmDefinitionLabel
    lab signatureDefinitionLabel
    lab signatureVerificationAlgorithmDefinitionLabel
    lab signatureSpaceDefinitionLabel
    lab signingKeySpaceDefinitionLabel
    lab verificationKeySpaceDefinitionLabel
    lab keyPairDistributionDefinitionLabel
    s ["Let", m ssp_, "be a", signatureSpace' <> ",", m sigsp_, "a", signingKeySpace', and, m versp_, "a", verificationKeySpace']
    newline
    s ["A", digitalSignatureScheme', "consists of three algorithms as follows"]
    itemize $ do
        item $ s ["A probabillistic", keyGenerator', "algorithm which generates a", keyPair <> ", consisting of a", signingKey', "(" <> secretKey <> ")", anda, signatureVerificationKey', "(" <> publicKey <> ")", "according to some", keyPairDistribution', over, m $ sigsp_ ⨯ versp_]
        let sig = "s"
        item $ s ["A probabillistic", signingAlgorithm', m signf_, "that takes as inputs a", signingKey, anda, message, "and computes the", signature', m $ sig ∈ ssp_, "for the", message]
        item $ s ["A deterministic", signatureVerificationAlgorithm', "that takes as inputs a", signatureVerificationKey <> ", a", message, anda, signature, "and outputs a bit that can be interpreted as", dquoted "accept", or, dquoted "reject"]
    s ["For every", keyPair <> ", the", signatureVerificationAlgorithm, m verif_, "must accept the signature computed by the", signingAlgorithm]

    todo "formalize"


signatureForgeryGameDefinition :: Note
signatureForgeryGameDefinition = de $ do
    lab signatureForgeryGameDefinitionLabel
    let t = "t"
    s [the, m t <> "-" <> message, signatureForgeryGame', "between an", adversary, anda, challenger, "is played as follows"]
    enumerate $ do
        item $ s [the, challenger, "uses the", keyGenerator, "to generate a", keyPair, "and sends the", signatureVerificationKey, "to the", adversary]
        item $ s [the, adversary, "can ask up to", m t, "arbitrary", messages, "to be signed by the", challenger]
        item $ s [the, adversary, "chooses a", message, anda, signature, "and wins the game if the", signature, "is a valid", signature, "for the", message, "and the", message, "was not queried yet"]

digitalSignatureSecurity :: Note
digitalSignatureSecurity = de $ do
    s ["A", digitalSignatureScheme, "is said to be", dquoted "secure against existential forgery under a chosen-message attack", "if no feasible", adversary, "can win the", signatureForgeryGame, "with a non-negligible", probability]

oneTimeSignatureSchemeDefinition :: Note
oneTimeSignatureSchemeDefinition = de $ do
    lab oneTimeSignatureSchemeDefinitionLabel
    s ["A", oneTimeSignatureScheme', "is a", digitalSignatureScheme, "that is", m 1 <> "-" <> message, "secure in the", signatureForgeryGame]

lamportOneTimeSignatureSchemeDefinition :: Note
lamportOneTimeSignatureSchemeDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
        f_ = "f"
        f = fn f_
        n = "n"
    s ["Let", m $ fun f_ xx yy, "be a", function, and, m $ n ∈ nats0]
    s ["Let", m $ msp_ =: bitss n, "be the", messageSpace <> ",", m $ ssp_ =: xx ^ n, "the", signatureSpace <> "," , m $ versp_ =: yy ^ (2 * n), "the", verificationKeySpace, and, m $ sigsp_ =: xx ^ (2 * n), "the", signingKeySpace]

    newline
    s ["The", lamportOneTimeSignatureScheme', "for", m f_, "is defined as follows"]

    itemize $ do
        let i = "i"
            b = "b"
        let x i b = "x" !: cs [i, b]
        let y i b = "y" !: cs [i, b]
        let z = "z"
            v = "v"
        let mesg = "m"
            m1 = mesg !: 1
            m2 = mesg !: 2
            mi = mesg !: i
            mn = mesg !: n
        let sig = "s"
            s1 = sig !: 1
            s2 = sig !: 2
            si = sig !: i
            sn = sig !: n
        item $ do
            s ["Let the", keyPairDistribution, "be the", probabilityDistribution, "induced as follows"]
            s ["First the", keyGenerator, "chooses uniformly at random", m $ 2 * n, elements, from, m xx]
            let xs = cs [x 0 1, x 1 1, x 0 2, x 1 2, dotsc, x 0 n, x 1 n]
            ma $ xs ∈ xx
            s ["Then it computes", m $ 2 * n, elements, "in", m yy, "from those", elements, "of", m xx]
            let ys = cs [y 0 1, y 1 1, y 0 2, y 1 2, dotsc, y 0 n, y 1 n]
            ma $ y i b =: f (x i b)
            ma $ ys ∈ yy
            s [the, signingKey, is, m $ z =: xs, "and the", verificationKey, is, m $ v =: ys]
        item $ do
            s [the, signingAlgorithm, "is deterministically defined as follows"]
            s ["Let", m $ mesg =: veclist m1 m2 mn ∈ msp_, "be a", message]
            ma $ sign mesg z =: veclist (x m1 1) (x m2 2) (x mn n) ∈ ssp_
        item $ do
            s [the, signatureVerificationAlgorithm, "is defined as follows"]
            s ["Let", m $ sig =: veclist s1 s2 sn ∈ msp_, "be a", signature]
            ma $ veri mesg sig v ⇔ fa (i ∈ setlist 1 2 n) (f (si) =: y mi i)

        item $ do
            s ["Note that this", digitalSignatureScheme, "is in fact correct"]
            ma $ fa (i ∈ setlist 1 2 n) $ f (x mi i) =: y mi i
            ma $ fa (cs [mesg ∈ msp_, v, z]) $ veri mesg (sign mesg z) v






lamportSecureIfOneWayFunction :: Note
lamportSecureIfOneWayFunction = thm $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
        f_ = "f"
        n = "n"
    s ["Let", m $ fun f_ xx yy, "be a", function, and, m $ n ∈ nats0]
    s ["If", m f_, "is a", oneWayFunction <> ",", "then its", lamportOneTimeSignatureScheme, "is in fact a", oneTimeSignatureScheme]
    let a = alpha
    s ["More precicely, any", adversary, "that can win a", nMesg 1, signatureForgeryGame, with, advantage, m a, "can be used to build an algorithm that wins the", functionInversionGame, with, advantage, m $ a / (2 * n)]

    toprove




hashFunctionDefinition :: Note
hashFunctionDefinition = de $ do
    lab hashFunctionDefinitionLabel
    let d = "D"
        r = "R"
    s ["A", hashFunction', "is a", function, m $ fun hshf_ d r, "where", m $ setsize d, "is (much) larger than", m $ setsize r]
    s ["Elements of", m d, "are called", hashes']
    let k = "k"
    s ["Typically", m $ d =: bitss "*", and, m $ r =: bitss k, "for some suitable", m $ nat k]

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
    s ["A parametrized family", m $ setcmpr hc (c ∈ cc), "of", hashFunctions, "is called", collisionResistant', "if no feasible", adversary, "can win the", collisionFindingGame, "with a non-negligible", probability, "for a", hashFunction, m hc, "(known to the", adversary <> ") chosen uniformly at random from the family of", hashFunction]

cryptoRefs :: Note
cryptoRefs = do
    nocite $ Reference "book" "cryptography-foundations" $
        [ ("author", "Ueli Maurer")
        , ("title", "Cryptography Foundations")
        , ("year", "2016")
        ]
