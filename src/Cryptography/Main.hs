module Cryptography.Main where

import           Notes

import           Functions.Basics.Macro
import           Functions.Basics.Terms

import           Cryptography.Macro
import           Cryptography.Terms

cryptography :: Note
cryptography = chapter "Cryptography" $ do
    cryptographicSchemeDefinition
    cryptographicProtocolDefinition
    symmetricCryptosystemDefinition

cryptographicSchemeDefinition :: Note
cryptographicSchemeDefinition = de $ do
    lab cryptographicSchemeDefinitionLabel
    s ["A", cryptographicScheme', or, cryptosystem']

cryptographicProtocolDefinition :: Note
cryptographicProtocolDefinition = de $ do
    lab cryptographicProtocolDefinitionLabel
    s ["A", cryptographicProtocol']

symmetricCryptosystemDefinition :: Note
symmetricCryptosystemDefinition = de $ do
    lab symmetricCryptosystemDefinitionLabel
    s ["A", symmetricCryptosystem', "for a", messageSpace, m msp_, ", ", ciphertextSpace, m csp_, ", ", keySpace, m ksp_, and, randomnessSpace, m rsp_, "is a pair of", functions, m $ tuple enc_ dec_, "as follows"]
    itemize $ do
        item $ do
            s [m enc_, "is called an", encryptionFunction', "and must be a", total, function]
            ma $ fun3 enc_ msp_ ksp_ rsp_ csp_
        item $ do
            s [m dec_, "is called a", decryptionFunction', "and it is usually strictly a", partialFunction]
            ma $ fun2 dec_ csp_ ksp_ msp_
