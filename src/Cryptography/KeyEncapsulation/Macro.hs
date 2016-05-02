module Cryptography.KeyEncapsulation.Macro where

import           Types

import           Functions.Application.Macro
import           Macro.Tuple

-- | Key encapsulation function
kem :: Note -> Note -> Note -> Note
kem = triple

-- | Keypair distribution
kpdist_ :: Note
kpdist_ = "D"

-- | Encapsulation function
encapf_ :: Note
encapf_ = "E"

-- | Encapsulate a public key
encap :: Note -> Note
encap = fn encapf_

-- | Decapsulation function
decapf_ :: Note
decapf_ = "d"

-- | Decapsulate a symmetric key
decap :: Note -> Note -> Note
decap = fn2 decapf_

-- | Concrete key encapsulation function
kem_ :: Note
kem_ = kem kpdist_ encapf_ decapf_

-- | The empty value of the decapsulation function
undef :: Note
undef = comm0 "bot"

