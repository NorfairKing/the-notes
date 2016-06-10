module Cryptography.ManyTimePadAttack where


import           Notes                                    hiding (cyclic,
                                                           inverse)

import           Codec.Picture.Png                        (decodePng, writePng)
import           Codec.Picture.Types                      (DynamicImage (..),
                                                           Image (..),
                                                           Pixel (..),
                                                           PixelRGB8 (..),
                                                           generateFoldImage,
                                                           pixelMapXY)
import           Control.Monad                            (replicateM, unless)
import qualified Data.Bits                                as B (Bits (..))
import qualified Data.ByteString                          as SB
import           Data.FileEmbed                           (embedFile)
import           System.Directory                         (doesFileExist)
import           Utils

import           Prelude                                  (Bool (..),
                                                           Either (..), Int,
                                                           error, mapM, snd,
                                                           (<$>))
import qualified Prelude                                  as P (and)

import           Cryptography.SymmetricCryptography.Terms


manyTimePadAttack :: Note
manyTimePadAttack = do
    imageExample


smileyImageBS :: SB.ByteString
smileyImageBS = $(embedFile "src/Cryptography/smiley.png")

sendCashImageBS :: SB.ByteString
sendCashImageBS = $(embedFile "src/Cryptography/sendcash.png")


imageExample :: Note
imageExample = ex $ do
    -- We will asume everything stays fine
    -- TODO replace with a dummy image if something goes wrong, and log an error.
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
    -- One less would not work. One more wouldn't either.
    let pixels =  width * height

    -- Generate that amount of bytes
    keyBS <- replicateM pixels random :: Note' [Bool]

    -- Now generate an image with this data.
    let keyImage :: Image PixelRGB8
        keyImage = snd $ generateFoldImage fun keyBS width height
          where
            fun :: [Bool] -> Int -> Int -> ([Bool], PixelRGB8)
            fun (True:rest)  _ _ = (rest, PixelRGB8 0xff 0xff 0xff)
            fun (False:rest) _ _ = (rest, PixelRGB8 0x00 0x00 0x00)
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

