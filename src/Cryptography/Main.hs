module Cryptography.Main where

import           Notes                                    hiding (cyclic,
                                                           inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Inverse.Terms
import           Functions.Jections.Terms
import           Groups.Macro
import           Groups.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro
import           Probability.ConditionalProbability.Macro
import           Probability.Independence.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Relations.Orders.Macro
import           Rings.Macro
import           Rings.Terms
import           Sets.Basics.Terms

import           Cryptography.ComputationalProblems
import           Cryptography.ComputationalProblems.Terms
import           Cryptography.Macro
import           Cryptography.MACs
import           Cryptography.SymmetricCryptography
import           Cryptography.SymmetricCryptography.Macro
import           Cryptography.SymmetricCryptography.Terms
import           Cryptography.SystemAlgebra
import           Cryptography.Terms

cryptography :: Note
cryptography = chapter "Cryptography" $ do
    symmetricCryptographyS
    mACS

    section "Key agreement" $ do
        diffieHellmanProtocolDefinition
        diffieHellmanManInTheMiddleAttack

    computationalProblemsS

    section "Public key encryption" $ do
        publicKeyEncryptionSchemeDefinition
        iNDCCASecureDefinitionPKEDefinition
        pKEINDCCASecureDefinition
        diffieHellmanPKEDefinition
        elGamalSchemeDefinition
        elGamalSchemeCPASecure
        elGamalSchemeNotCCASecure

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

    section "Digital signatures" $ do
        digitalSignatureDefinition
        signatureForgeryGameDefinition
        digitalSignatureSecurity

    section "Hash functions" $ do
        hashFunctionDefinition
        collisionFindingGameDefinition
        collisionResistantDefinition

    systemAlgebraS

    cryptoRefs


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

additiveDLEasy :: Note
additiveDLEasy = thm $ do
    let n = "n"
    s [the, discreteLogarithm, "problem is trivially solvable in the", group, m $ intagrp n]
    proof $ do
        let z = "z"
            a = "a"
            g = "g"
        s ["Recall that, for any element", m (z ∈ intmod n) <> ", we are looking for the integer", m $ integer a, "such that", m $ z =: g * a, "where", m g, "is a", generator, "of", m $ intagrp n]
        s ["Luckily, ", m $ intagrp n, "gives rise to a", ring, m $ intring n, "as well"]
        s ["This allows us to find", m a, "by dividing", m z, by, m g]
        s ["More precicely: because", m g, "is a", generator, "means that", m g, "must have a multiplicative inverse in", m $ intring n, "otherwise no multiple of", m g, "would be equal to", m 1]
        s ["Now the only thing we need to do is go through the", elements, "of", m $ intmod n, "multiply each of them by", m g, "in", m $ intring n, "and check if the result equals", m 1, "to find the multiplicative inverse", m $ rinv g, "of", m g, "in", m $ intring n]
        s ["We then compute", m a, "by evaluating", m $ rinv g * z =: rinv g * g * a =: a]
        s ["We could also use the extended Euclidean algorithm to find", m $ rinv g, "even more efficiently"]
        refneeded "Extended Euclidean algorithm"

dlReducable :: Note
dlReducable = thm $ do
    let g = "g"
        h = "h"
    s [the, discreteLogarithm, "problem in a", group, m grp_, "for a", generator, m g, "is reducable to the", discreteLogarithm, "problem in that same", group, "but for a different", generator]

    proof $ do
        let a = "A"
        s ["Let", m a, "be an algorithm that solves the", discreteLogarithm, "problem for a", generator, m g]
        s ["We construct an algorithm that solves the", discreteLogarithm, "problem for another", generator, m h, "of", m grp_, "as follows"]
        let z = "z"
            b = "b"
            c = "c"
        s ["Let", m z, "be the", group, element, "that we want the", discreteLogarithm, m b, "base", m h, "in", m grp_, "of"]
        s ["There then exists a", m $ integer c, "such that", m c, "is the", discreteLogarithm, "base", m g, "in", m grp_, "of", m z]
        ma $ z =: h ^ b =: g ^ c
        let d = "d"
        s ["Because", m h, "is an", element, "of", m grps_ <> ",", "there exists a", m $ integer d, "such that", m $ h =: g ^ d, "holds"]
        ma $ z =: (pars $ g ^ d) ^ b =: g ^ c
        s ["This means that we have the following equation for", m c, "in", m $ intring $ ord grps_]
        ma $ d * b =: c
        s ["The algorithm now uses", m a, "to find", m c, from, m z, and, m d, from, m h]
        s ["It then computes the multiplicative inverse of", m d, "in", m $ intring $ ord grps_, "with the extended Euclidean algorithm and finally computes", m b, "by evaluating", m $ rinv d * c =: rinv d * d * b =: b]

dlModTwoInEvenOrderGroup :: Note
dlModTwoInEvenOrderGroup = thm $ do
    let n = "n"
    s ["Let", m grp_, beA, group, with, "an even", order, m $ ord grp_ =: 2 * n]
    s ["There exists an efficient algorithm to compute whether the", discreteLogarithm, "of an", element, "is even or not"]

    proof $ do
        let x = "x"
        s ["Let", m x, beAn, element, "of", m grps_]
        let g = "g"
            a = "a"
        s ["For a given base", m g, "the task is to compute", m $ a `mod` 2, "such that", m $ x =: g ^ a, "holds"]
        let q = "q"
            r = "r"
        s ["Define", m q, and, m r, "as the quotient and rest after division by", m 2, "of", m a]
        s ["Observe first the following"]
        ma $ x ^ n =: g ^ (a * n) =: g ^ ((pars $ 2 * q + r) * n) =: g ^ (2 * n * q) ** (g ^ (r * n) =: g ^ (r * n))
        s ["This means that", m $ x ^ n, "will be equal to the", neutralElement, "if", m a, "is even and", m $ g ^ n, "(which cannot be the", neutralElement <> ") if", m a, "is odd"]
        s ["We only have to compare", m $ x ^ n, "to the", neutralElement, "to determine", m $ a `mod` 2]


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


cryptoRefs :: Note
cryptoRefs = do
    nocite $ Reference "book" "cryptography-foundations" $
        [ ("author", "Ueli Maurer")
        , ("title", "Cryptography Foundations")
        , ("year", "2016")
        ]
