module Cryptography.SystemAlgebra where

import           Notes

import           Cryptography.SystemAlgebra.AbstractSystems
import           Cryptography.SystemAlgebra.DiscreteSystems
import           Cryptography.SystemAlgebra.SecureChannels

systemAlgebraS :: Note
systemAlgebraS = section "System Algebra" $ do
    abstractSystemsSS
    discreteSystemsSS
    secureChannelsSS

