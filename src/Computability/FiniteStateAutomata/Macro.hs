module Computability.FiniteStateAutomata.Macro where

import           Types

import           Macro.Tuple



-- * Automata
-- ** NFSA

-- | NFSA definition
nfsa :: Note -- ^ Alphabet
     -> Note -- ^ Set of states
     -> Note -- ^ Set of initial states
     -> Note -- ^ Set of accepting states
     -> Note -- ^ Transition function
     -> Note
nfsa = quintuple

-- | Concrete NFSA
nfsa_ :: Note
nfsa_ = "hi"

-- ** DFSA
