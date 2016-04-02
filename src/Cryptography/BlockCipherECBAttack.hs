module Cryptography.BlockCipherECBAttack where

import           Notes                                    hiding (cyclic,
                                                           inverse)

import           Codec.Picture.Png                        (decodePng, writePng)
import           Codec.Picture.Types                      (DynamicImage (..),
                                                           Image (..),
                                                           Pixel (..),
                                                           PixelRGBA8 (..),
                                                           generateFoldImage)
import           Control.Monad                            (forM, forM_,
                                                           replicateM, unless)
import qualified Data.Bits                                as B (Bits (..))
import qualified Data.ByteString                          as SB
import           Data.FileEmbed                           (embedFile)
import           Data.List                                (cycle)
import qualified Data.Text                                as T
import           System.Directory                         (doesFileExist)
import           Utils

import           Prelude                                  (Bool (..),
                                                           Either (..), Int,
                                                           error, map, mapM,
                                                           return, snd, zip,
                                                           (++), (<$>))
import qualified Prelude                                  as P (and)

import           Cryptography.SymmetricCryptography.Terms


blockCipherECBAttack :: Note
blockCipherECBAttack = do
    eCBInsecureExample

tuxImageBS :: SB.ByteString
tuxImageBS = $(embedFile "src/Cryptography/tux.png")



xorPixel :: PixelRGBA8 -> PixelRGBA8 -> PixelRGBA8
xorPixel (PixelRGBA8 r1 g1 b1 a1) (PixelRGBA8 r2 g2 b2 a2)
    = (PixelRGBA8 (r1 `B.xor` r2) (g1 `B.xor` g2) (b1 `B.xor` b2) (a1 `B.xor` a2))

eCBInsecureExample :: Note
eCBInsecureExample = ex $ do
    -- We will asume everything stays fine
    let fromRight (Right a) = a
        fromRight _ = error "there was an error decoding the images"

    -- Get the tux image
    let (ImageRGBA8 tuxImg) = fromRight $ decodePng tuxImageBS

    let width = (imageWidth tuxImg)
        height = (imageHeight tuxImg)

    let cipherImage :: Int -> Note' (Image PixelRGBA8)
        cipherImage keylen = do
            -- Make a tiny list of pixels
            pixelKey <- replicateM keylen $ do
                -- Generate 4 random bytes to build a single pixel
                r <- random
                g <- random
                b <- random
                a <- random
                return $ PixelRGBA8 r g b a
            return $ img pixelKey
          where
            img pixelKey = snd $ generateFoldImage fun (cycle pixelKey) width height

            fun :: [PixelRGBA8] -> Int -> Int -> ([PixelRGBA8], PixelRGBA8)
            fun (p:ps) x y = (ps, (pixelAt tuxImg x y) `xorPixel` p)
            fun _ _ _ = error "Something went wrong while generating a weird penguin."

    let blockSizes = [1, 2, 3, 4, 5, 10, 25, 50, 100, 250, 500, 1000, 2500, 5000, 10000] :: [Int]

    let tuxFP = "tux.png"
        encTuxFPs = map (\i -> "tux_enc" ++ show i ++ ".png") blockSizes
        allFiles = tuxFP : encTuxFPs

    cImages <- forM blockSizes cipherImage

    doneAlready <- liftIO $ P.and <$> mapM doesFileExist allFiles
    unless doneAlready $ do
        registerAction tuxFP $ writePng tuxFP tuxImg
        forM_ (zip cImages encTuxFPs) $ \(i, fp) ->
            registerAction fp $ writePng fp i

    s ["The following is an application of the above theorem to a concrete situation with an image"]
    s ["Suppose we have an image as a message"]
    hereFigure $ do
        include tuxFP
        caption "An image as a message"
    s ["If we use a", blockCipher, "in", electronicCodebook, "mode", "the result of the encryption will still resemble the message"]
    hereFigure $ do
        let chs = chunk 5 encTuxFPs
        forM_ chs $ \fps -> do
            forM_ fps include
            newline
        caption $ s ["The encryption with a random", blockCipher, "in", eCB, "mode for block sizes", csa $ map (raw . T.pack . show) blockSizes]
    s ["In this case we used a", blockCipher, "with various", blockLengths]
    s ["As the", encryptionFunction, "we used the XOR with a randomly chosen", key]
    s ["The greater the", blockLengths <> ", the more this method will resemble the", oneTimePad]
  where
    include = includegraphics
                [ KeepAspectRatio True
                , IGHeight (Cm 3.0)
                , IGWidth (CustomMeasure $ "0.5" <> textwidth)
                ]

