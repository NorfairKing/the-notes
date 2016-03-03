-- The following implementation is by no means intended to be secure.
-- It should only be used to show examples of results
module Cryptography.OTP.Impl where

import           Control.Monad   (replicateM)
import           Data.Bits
import qualified Data.ByteString as SB
import           Data.Word
import           Numeric         (showHex, showIntAtBase)
import           Prelude
import           Types
import           Utils

liftBS :: (Word8 -> Word8) -> (SB.ByteString -> SB.ByteString)
liftBS fun = SB.pack . map fun . SB.unpack

liftBS2 :: (Word8 -> Word8 -> Word8) -> (SB.ByteString -> SB.ByteString -> SB.ByteString)
liftBS2 fun a b = SB.pack $ zipWith fun (SB.unpack a) (SB.unpack b)

instance Bits SB.ByteString where
    (.&.) = liftBS2 (.&.)
    (.|.) = liftBS2 (.|.)
    xor = liftBS2 xor
    complement = liftBS complement
    -- TODO later if I need them.
    shift = undefined
    rotate = undefined
    bitSize = undefined
    bitSizeMaybe = undefined
    isSigned = undefined
    testBit = undefined
    bit = undefined
    popCount = undefined

type OTPKey = SB.ByteString
type OTPMessage = SB.ByteString
type OTPCipherText = SB.ByteString

otpEncrypt :: OTPKey -> OTPMessage -> OTPCipherText
otpEncrypt = xor

otpDecrypt :: OTPKey -> OTPCipherText -> OTPMessage
otpDecrypt = xor

hexBS :: SB.ByteString -> String
hexBS = concatMap (pad 2 '0' . flip showHex "") . SB.unpack

hexBS' :: SB.ByteString -> String
hexBS' = unwords . map (pad 2 '0' . flip showHex "") . SB.unpack

pad1 :: String -> String
pad1 [] = "00"
pad1 [c] = '0' : [c]
pad1 s = s

binBS :: SB.ByteString -> String
binBS = concatMap (pad 8 '0' . flip (showIntAtBase 2 binary) "") . SB.unpack

binBS' :: SB.ByteString -> String
binBS' = unwords . map (pad 8 '0' . flip (showIntAtBase 2 binary) "") . SB.unpack

binary :: Int -> Char
binary 0 = '0'
binary 1 = '1'
binary n = error $ "not in binary spectrum: " ++ show n


pad :: Int -> Char -> String -> String
pad n c s
    | length s < n = replicate (n - length s) c ++ s
    | otherwise = s

getKeyFor :: SB.ByteString -> Note' SB.ByteString
getKeyFor mesg = SB.pack <$> replicateM (SB.length mesg) random




