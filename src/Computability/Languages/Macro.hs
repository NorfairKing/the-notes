module Computability.Languages.Macro where

import           Types

import           Macro.MetaMacro


import           Computability.Symbols.Macro

-- * Languages

-- | Concrete Language
lan_ :: Note
lan_ = "L"

-- ** Concatenation

-- | Language concatenation
clconcat :: [Note] -> Note
clconcat = mconcat

-- | Infix operator for language concatenation
(<@@>) :: Note -> Note -> Note
(<@@>) = (<>)


-- ** Language power

-- | Power(set) of language
lanpow :: Note -> Note -> Note
lanpow = (^:)

-- | Infix operator for power of language
(^@:) :: Note -> Note -> Note
(^@:) = lanpow

-- ** Operations on languages

-- | Kleene star
ks :: Note -> Note
ks l = l ^: "*"

-- | Language plu
lp :: Note -> Note
lp l = l ^: "+"

-- | Languages over alphabet
loa :: Note -> Note
loa s = lan_ !: s

-- | Languages over concrete alphabet
loa_ :: Note
loa_ = loa alph_

-- ** Reverse language

-- | Reverse language of a given language
rlan :: Note -> Note
rlan lan = lan ^: "R"



