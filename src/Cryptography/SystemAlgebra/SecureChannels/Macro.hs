module Cryptography.SystemAlgebra.SecureChannels.Macro where

import           Types

import qualified Data.Text    as T
import           Prelude      (Int, id)

import           Macro.Arrows

-- * Channels

bullet :: Note
bullet = comm0 "bullet"

negSpace :: Int -> Note
negSpace n = commS "kern" <> raw ("-" <> T.pack (show n) <> "px")

-- | Communication channel
comC :: Note
comC = longrightarrow

-- | Authenticated channel
autC :: Note
autC = bullet <> negSpace 4 <> longrightarrow

-- | Authenticated channel Backwards
autCB :: Note
autCB = longleftarrow <> negSpace 6 <> bullet

-- | Secret channel
secrC :: Note
secrC = longrightarrow <> negSpace 6 <> bullet

-- | Secure channel
secuC :: Note
secuC = bullet <> negSpace 4 <> longrightarrow <> negSpace 6 <> bullet

-- | Key channel
keyC :: Note
keyC = bullet <> negSpace 7 <> raw "=\\joinrel=\\joinrel=" <> negSpace 6 <> bullet

-- | Half key channel
hkeyC :: Note
hkeyC = raw "=\\joinrel=\\joinrel=" <> negSpace 6 <> bullet


-- | Encryption transformer
encT :: Note -- ^ Encryption function
     -> Note
encT = id

-- | Encryption transformer for @enc_@
encT_ :: Note
encT_ = encT "enc"

-- | Decryption transformer
decT :: Note -- ^ Decryption function
     -> Note
decT = id

-- | Decryption transformer for @dec_@
decT_ :: Note
decT_ = decT "dec"
