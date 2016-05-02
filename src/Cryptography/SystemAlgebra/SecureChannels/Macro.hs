module Cryptography.SystemAlgebra.SecureChannels.Macro where

import           Types

import qualified Data.Text    as T
import           Macro.Math
import           Prelude      (Int, id)

import           Macro.Arrows

-- * Channels
negSpace :: Int -> Note
negSpace n = commS "kern" <> raw ("-" <> T.pack (show n) <> "px")

-- | To turn a channel symbol into one with a message space
withms :: Note -> Note -> Note
withms chan n = overset n chan

-- | Communication channel
comC :: Note -> Note
comC = withms comC_

-- | Communication channel with implicit message space
comC_ :: Note
comC_ = longrightarrow

-- | Communication channel with deletion
comCwd :: Note -> Note
comCwd = withms comCwd_

-- | Communication channel with deletion with implicit message space
comCwd_ :: Note
comCwd_ = "-" <> rightarrow

-- | Authenticated channel
autC :: Note -> Note
autC = withms autC_

-- | Authenticated channel with implicit message space
autC_ :: Note
autC_ = bullet <> negSpace 4 <> longrightarrow

-- | Authenticated channel with deletion
autCwd :: Note -> Note
autCwd = withms autCwd_

-- | Authenticated channel with deletion with implicit message space
autCwd_ :: Note
autCwd_ = bullet <> negSpace 4 <> "-" <> rightarrow

-- | Authenticated channel with deletion Backwards
autCBwd :: Note -> Note
autCBwd = withms autCB_

-- | Authenticated channel with deletion Backwards with implicit message space
autCBwd_ :: Note
autCBwd_ = leftarrow <> "-" <> negSpace 6 <> bullet

-- | Authenticated channel Backwards
autCB :: Note -> Note
autCB = withms autCB_

-- | Authenticated channel Backwards with implicit message space
autCB_ :: Note
autCB_ = longleftarrow <> negSpace 6 <> bullet

-- | Secret channel
secrC :: Note -> Note
secrC = withms secrC_

-- | Secret channel with implicit message space
secrC_ :: Note
secrC_ = longrightarrow <> negSpace 6 <> bullet

-- | Secret channel with deletion
secrCwd :: Note -> Note
secrCwd = withms secrCwd_

-- | Secret channel with deletion with implicit message space
secrCwd_ :: Note
secrCwd_ = "-" <> rightarrow <> negSpace 6 <> bullet

-- | Secure channel
secuC :: Note -> Note
secuC = withms secuC_

-- | Secure channel with implicit message space
secuC_ :: Note
secuC_ = bullet <> negSpace 4 <> longrightarrow <> negSpace 6 <> bullet

-- | Secure channel with deletion
secuCwd :: Note -> Note
secuCwd = withms secuCwd_

-- | Secure channel with deletion with implicit message space
secuCwd_ :: Note
secuCwd_ = bullet <> negSpace 4 <> "-" <> rightarrow <> negSpace 6 <> bullet

-- | Key channel
keyC :: Note
keyC = bullet <> negSpace 7 <> raw "=\\joinrel=\\joinrel=" <> negSpace 6 <> bullet

-- | Unilateral key channel
ukeyC :: Note -> Note
ukeyC = withms ukeyC_

-- | Unilateral key channel with implict message space
ukeyC_ :: Note
ukeyC_ = raw "=\\joinrel=\\joinrel=" <> negSpace 6 <> bullet


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

-- | 'deliver' message
deliverM :: Note
deliverM = "deliver"

-- | KEM enc transformer
encapT_ :: Note
encapT_ = "encap"

-- | KEM dec transformer
decapT_ :: Note
decapT_ = "decap"
