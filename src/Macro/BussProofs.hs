module Macro.BussProofs where

import           Types

-- * Raw commands

-- | AxiomC with no arguments
axiomC :: Note
axiomC = comm0 "AxiomC"

-- | AxiomC with one argument
axiomC_ :: Note -> Note
axiomC_ = comm1 "AxiomC"

-- | LeftLabel
leftLabel :: Note -> Note
leftLabel = comm1 "LeftLabel"

-- | UnaryInfC
unaryInfC :: Note -> Note
unaryInfC = comm1 "UnaryInfC"

-- | BinaryInfC
binaryInfC :: Note -> Note
binaryInfC = comm1 "BinaryInfC"

-- | TrinaryInfC
trinaryInfC :: Note -> Note
trinaryInfC = comm1 "TrinaryInfC"

-- * Environment
prooftree :: LaTeXC l => l -> l
prooftree = liftL $ TeXEnv "prooftree" []

-- * Easier usage

unaryInf :: Note -- ^ Label
         -> Note -- ^ Above part
         -> Note -- ^ Content
         -> Note
unaryInf l a c = a <> leftLabel l <> unaryInfC c

binaryInf :: Note -- ^ Label
          -> Note -- ^ Left part
          -> Note -- ^ Right part
          -> Note -- ^ Content
          -> Note
binaryInf lab l r c = l <> r <> leftLabel lab <> binaryInfC c

trinaryInf :: Note -- ^ Label
           -> Note -- ^ Left part
           -> Note -- ^ Middle part
           -> Note -- ^ Right part
           -> Note -- ^ Content
           -> Note
trinaryInf lab l m r c = l <> m <> r <> leftLabel lab <> trinaryInfC c

