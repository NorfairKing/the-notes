module Computability.FiniteStateAutomata.Macro where

import           Types

import           Macro.MetaMacro
import           Macro.Tuple



-- * Automata
-- ** NFSA

-- | NFSA definition
nfsa :: Note -- ^ Set of states
     -> Note -- ^ Alphabet
     -> Note -- ^ Transition function
     -> Note -- ^ Set of accepting states
     -> Note -- ^ Set of initial states
     -> Note
nfsa = quintuple

-- | Concrete NFSA
nfsa_ :: Note
nfsa_ = "hi"

-- | Concrete set of NFSA states
nfas_ :: Note
nfas_ = "Q"

-- | Concrete NFSA transition function
nfatf_ :: Note
nfatf_ = delta

-- | Starting state
nfass_ :: Note
nfass_ = "q" !: "s"

-- | Appecting states
nfaas_ :: Note
nfaas_ = "F"

-- ** DFSA
