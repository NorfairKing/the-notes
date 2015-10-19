module Macro.Computability.Macro where

import           Macro.Math
import           Macro.MetaMacro
import           Types

-- Computability Symbol Equality
csymEqSign :: Note
csymEqSign = underset "s" "="

csymEq :: Note -> Note -> Note
csymEq = binop csymEqSign

(=@=) :: Note -> Note -> Note
(=@=) = csymEq

-- Computability Alphabet
calph :: Note
calph = comm0 "Sigma"

-- Computability String
cstr :: Note
cstr = "s"

cstrlst :: Note -> Note -> Note
cstrlst s1 sn = s1 <> dotsc <> sn

cstrlist :: Note -> Note -> Note -> Note
cstrlist s1 s2 sn = s1 <> s2 <> dotsc <> sn

cstrof :: [Note] -> Note
cstrof = mconcat

cestr :: Note
cestr = epsilon

-- Computability concatenation
cconcat :: [Note] -> Note
cconcat = mconcat

(<@>) :: Note -> Note -> Note
(<@>) = (<>)

-- Computability Strings of Alphabet
cstrsof :: Note -> Note
cstrsof alphabet = alphabet ^: "*"

cstrs :: Note
cstrs = cstrsof calph

-- Computability Reverse String
crstr :: Note -> Note
crstr s = s ^: "R"

-- Computability Aplhabet and empty
calphe :: Note
calphe = calph !: cestr

-- Computability Language
clan :: Note
clan = "L"

-- Computability language concatenation
clconcat :: [Note] -> Note
clconcat = mconcat

(<@@>) :: Note -> Note -> Note
(<@@>) = (<>)

-- Computability language power
clanpow :: Note -> Note -> Note
clanpow = (^:)

(^@:) :: Note -> Note -> Note
(^@:) = clanpow


-- Computability Kleene star
cks :: Note -> Note
cks l = l ^: "*"

-- Computability Language plus
clp :: Note -> Note
clp l = l ^: "+"

-- Computability languages over alphabet
cloa :: Note -> Note
cloa s = clan !: s

cls :: Note
cls =  cloa calph
