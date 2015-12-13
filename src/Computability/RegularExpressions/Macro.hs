module Computability.RegularExpressions.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro


import           Computability.Languages.Macro
import           Computability.Symbols.Macro

-- | Concrete Regular expression
re_ :: Note
re_ = "E"

-- * Regular expression definition

-- | Regular expression of empty string (epsilon)
rees :: Note
rees = epsilon

-- | Empty regular expression (phi)
ree :: Note
ree = phi

-- | Regular expression of concatenation
rec :: Note -> Note -> Note
rec m n = pars $ m <> n

-- | Infix operator for regular expression of concatenation
(<@@@>) :: Note -> Note -> Note
(<@@@>) = rec

-- | Regular expression of disjunction
red :: Note -> Note -> Note
red m n = pars $ m <> n

-- | Infix operator for regular expression of disjunction
(<@|@>) :: Note -> Note -> Note
(<@|@>) = red

-- | Regular expression for multiples (asterisk)
rea :: Note -> Note
rea n = pars n ^: "*"

-- * Operations on regular expressions

-- | Regexes over alphabet
reoa :: Note -> Note
reoa sigma = "RegEx" !: sigma

-- | Regexes over concrete alphabet
reoa_ :: Note
reoa_ = reoa alph_

-- | Language of regular expression
lre :: Note -> Note
lre e = lan_ !: e

-- | Language of concrete regular expression
lore :: Note
lore = lre re_

-- | Set of regular languages
reglan :: Note
reglan = "RegLan"

