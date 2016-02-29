module Cryptography.Main where

import           Notes

import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Logic.FirstOrderLogic.Macro
import           Sets.Basics.Terms

import           Cryptography.Macro
import           Cryptography.Terms

cryptography :: Note
cryptography = chapter "Cryptography" $ do
    cryptographicSchemeDefinition
    cryptographicProtocolDefinition
    symmetricCryptosystemDefinition
    deterministicCryptoSystem
    cipherDefinition

cryptographicSchemeDefinition :: Note
cryptographicSchemeDefinition = de $ do
    lab cryptographicSchemeDefinitionLabel
    s ["A", cryptographicScheme', or, cryptosystem', "consists of several", functions]

cryptographicProtocolDefinition :: Note
cryptographicProtocolDefinition = de $ do
    lab cryptographicProtocolDefinitionLabel
    s ["A", cryptographicProtocol', "for a given", set, "of parties consists of, for each party, a precicely specified behavior in the interaction with the other parties"]

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
    let k = "k"
        m = "m"
        r = "r"
    ma $ fa (k ∈ ksp_)
       $ fa (m ∈ msp_)
       $ fa (r ∈ rsp_)
       $ dec (enc m k r) k =: m

deterministicCryptoSystem :: Note
deterministicCryptoSystem = de $ do
    s ["A", deterministic', cryptosystem, "is a system in which the", randomnessSpace, "is entirely ignored"]
    s ["We then model the", encryptionFunction, "as taking only two arguments and leave out the", randomnessSpace]

cipherDefinition :: Note
cipherDefinition = de $ do
    lab cipherDefinitionLabel
    s ["A", cipher', "is a", deterministic, symmetricCryptosystem]
