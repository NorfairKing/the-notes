{-# LANGUAGE QuasiQuotes #-}
module Cryptography.Main where

import           Notes                                hiding (inverse)

import           Codec.Picture.Png                    (decodePng, writePng)
import           Codec.Picture.Types                  (DynamicImage (..),
                                                       Image (..), Pixel (..),
                                                       PixelRGB8 (..),
                                                       generateFoldImage,
                                                       pixelMapXY)
import           Control.Monad                        (replicateM, unless)
import qualified Data.Bits                            as B (Bits (..))
import qualified Data.ByteString                      as SB
import qualified Data.ByteString.Char8                as SB8
import           Data.FileEmbed                       (embedFile)
import qualified Data.Text                            as T
import           System.Directory                     (doesFileExist)
import           Utils

import           Prelude                              (Bool (..), Either (..),
                                                       Int, error, mapM, snd,
                                                       (<$>))
import qualified Prelude                              as P (and)

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
import           Cryptography.OTP.Impl
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
        oneTimePadExample
        oneTimePadSecure
        additiveStreamCipherDefinition

        subsection "IND-CPA" $ do
            indcpaDefinition
            indcpaSecurityDefinition

        subsection "IND-CCA" $ do
            indccaDefinition
            indccaSecurityDefinition

        manyTimePadInsecure

        subsection "pseudorandomness" $ do
            pseudoRandomGeneratorDefinition

        subsection "block ciphers" $ do
            blockCipherDefinition

    section "Message Authentication Codes" $ do
        messageAuthenticationCodeDefinition
        messageAuthenticationCodeSecurityDefinition

    section "Key agreement" $ do
        diffieHellmanProtocolDefinition


cryptographicSchemeDefinition :: Note
cryptographicSchemeDefinition = de $ do
    lab cryptographicSchemeDefinitionLabel
    s ["A", cryptographicScheme', or, cryptosystem', "consists of several", functions]

cryptographicProtocolDefinition :: Note
cryptographicProtocolDefinition = de $ do
    lab cryptographicProtocolDefinitionLabel
    lab protocolDefinitionLabel
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
    lab manyTimePadDefinitionLabel

    s [the, oneTimePad', "is a", cipher, "with the following", encryptionFunction, and, decryptionFunction]
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

    s ["Encrypting the message", quoted $ raw $ T.pack mesg, "(encoded with ASCII) with following the", oneTimePad, cipher, "with a random key, results in the following situation"]

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


oneTimePadSecure :: Note
oneTimePadSecure = do
    prop $ do
        let n = "n"
        s [the, oneTimePad <> "'s", ciphertexts, "are", independent, "of their", messages, "for a given message length", m n]
        toprove_ "page 17 of crypto"
    nte $ do
        let t = "t"
        s ["Note that we cannot say that the", oneTimePad, "is", iNDCPASecure, "nor", iNDCCASecure, "for any", m $ t >= 1, "because the", oneTimePad, "can, by definition, only be used once for the same key"]



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

smileyImageBS :: SB.ByteString
smileyImageBS = $(embedFile "src/Cryptography/smiley.png")

sendCashImageBS :: SB.ByteString
sendCashImageBS = $(embedFile "src/Cryptography/sendcash.png")

manyTimePadInsecure :: Note
manyTimePadInsecure = do
    thm $ do
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

    ex $ do
        -- We will asume everything stays fine
        let fromRight (Right a) = a
            fromRight _ = error "there was an error decoding the images"

        -- Get the smiley image
        let (ImageRGB8 smileyImg) = fromRight $ decodePng smileyImageBS

        -- Get the sendCash image
        let (ImageRGB8 sendCashImg) = fromRight $ decodePng sendCashImageBS

        -- This is how you XOR images
        let xorImages :: Image PixelRGB8 -> Image PixelRGB8 -> Image PixelRGB8
            xorImages i1 i2 = pixelMapXY fun i1
              where
                fun :: Int -> Int -> PixelRGB8 -> PixelRGB8
                fun x y p = p `xorPixel` pixelAt i2 x y

                xorPixel :: PixelRGB8 -> PixelRGB8 -> PixelRGB8
                xorPixel (PixelRGB8 r1 g1 b1) (PixelRGB8 r2 g2 b2)
                    = (PixelRGB8 (r1 `B.xor` r2) (g1 `B.xor` g2) (b1 `B.xor` b2))

        -- Width and height of our six images, they must all be the same.
        let width = (imageWidth smileyImg)
            height = (imageHeight smileyImg)

        -- The total number of random bypes required.
        -- One less would not work.
        let pixels = 3 * width * height

        -- Generate that amount of bytes
        keyBS <- replicateM pixels random :: Note' [Word8]

        -- Now generate an image with this data.
        let keyImage :: Image PixelRGB8
            keyImage = snd $ generateFoldImage fun keyBS width height
              where
                fun :: [Word8] -> Int -> Int -> ([Word8], PixelRGB8)
                fun (r:g:b:rest) _ _ = (rest, PixelRGB8 r g b)
                fun _ _ _ = error "incorrect number of random bytes supplied"

        -- Encrypt both of our images with the key image
        let encSmiley = xorImages keyImage smileyImg
        let encSendCash = xorImages keyImage sendCashImg

        -- Xor the encrypted messages for dramatic effect
        let encXORImg = xorImages smileyImg sendCashImg

        let keyFP = "key.png"
            smileyFP = "smiley.png"
            sendCashFP = "sendcash.png"
            encSmileyFP = "smiley_enc.png"
            encSendCashFP = "sendCash_enc.png"
            encXORFP = "xor_enc.png"
            allFiles =
                [ keyFP
                , smileyFP
                , sendCashFP
                , encSmileyFP
                , encSendCashFP
                , encXORFP
                ]

        doneAlready <- liftIO $ P.and <$> mapM doesFileExist allFiles
        unless doneAlready $ do
            registerAction smileyFP $ writePng smileyFP smileyImg
            registerAction sendCashFP $ writePng sendCashFP sendCashImg
            registerAction keyFP $ writePng keyFP keyImage
            registerAction encSmileyFP $ writePng encSmileyFP encSmiley
            registerAction encSmileyFP $ writePng encSendCashFP encSendCash
            registerAction encXORFP $ writePng encXORFP encXORImg

        -- Show it all to our reader
        s ["The following is an application of the above theorem to a concrete situation with images"]
        s ["Suppose we have messages in the form of images as follows"]
        hereFigure $ do
            include smileyFP
            hspace $ Cm 1
            include sendCashFP
            caption "Two messages in the form of images"

        s ["We decide to use the", oneTimePad, "so we generate a random", key]
        hereFigure $ do
            include keyFP
            caption "The key"

        s ["We forget about the requirement that the", oneTimePad, "can only be used once and use the key for both of our messages, thus making it a", manyTimePad]
        s ["The resulting encryptions look inconspicuous"]
        hereFigure $ do
            include encSmileyFP
            hspace $ Cm 1
            include encSendCashFP
            caption "The encrypted messages"

        s ["When we XOR the encryptions, however, the result is far from unintelligible"]
        hereFigure $ do
            include encXORFP
            caption "The XOR of the two encrypted messages"
        s ["You can clearly see that this image is the XOR of the two original messages"]
        s ["This is entirely insecure"]
  where
    include = includegraphics
                [ KeepAspectRatio True
                , IGHeight (Cm 3.0)
                , IGWidth (CustomMeasure $ "0.5" <> textwidth)
                ]

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


-- discreteLogarithmProblemDefinition :: Note
-- discreteLogarithmProblemDefinition = de $ do
--     s [the, discreteLogarithm', "problem", "for a", cyclic, group,
