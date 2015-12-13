module Computability.Symbols.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro

-- * Symbols
-- ** Symbol equality

-- | Symbol equality sign
symEqSign :: Note
symEqSign = underset "s" "="

-- | Symbol equality operation
symEq :: Note -> Note -> Note
symEq = binop symEqSign

-- | Infix symbol equality operator
(=@=) :: Note -> Note -> Note
(=@=) = symEq


-- * Alphabets

-- | Concrete alphabet
alph_ :: Note
alph_ = comm0 "Sigma"

-- | Concrete alphabet and string
alphe_ :: Note
alphe_ = alph_ !: estr

-- * Strings

-- | Empty string
estr :: Note
estr = epsilon

-- | Concrete string
str_ :: Note
str_ = "s"

-- | Strings of alphabet
strsof :: Note -> Note
strsof alphabet = alphabet ^: "*"

-- | Strings of concrete alphabet
strsof_ :: Note
strsof_ = strsof alph_

-- ** Lists of symbols
strlst :: Note -> Note -> Note
strlst s1 sn = s1 <> dotsc <> sn

strlist :: Note -> Note -> Note -> Note
strlist s1 s2 sn = s1 <> s2 <> dotsc <> sn

strof :: [Note] -> Note
strof = mconcat

-- ** Concatenation

-- | String concatenation
strconcat :: [Note] -> Note
strconcat = mconcat

-- | String concatenation infix operator
(<@>) :: Note -> Note -> Note
(<@>) = (<>)

-- ** Reverse String
-- | Reverse of a given string
rstr :: Note -> Note
rstr s = s ^: "R"



