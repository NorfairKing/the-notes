module Macro.Computability.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro

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

-- Computability reverse languages
crlan :: Note -> Note
crlan lan = lan ^: "R"

-- Computability Regular Expressions

-- empty
cree :: Note
cree = epsilon

-- phi
crep :: Note
crep = phi

-- concatenation
crec :: Note -> Note -> Note
crec m n = pars $ m <> n

(<@@@>) :: Note -> Note -> Note
(<@@@>) = crec

-- disjunction
cred :: Note -> Note -> Note
cred m n = pars $ m <> n

(<@|@>) :: Note -> Note -> Note
(<@|@>) = cred

-- asterisk
crea :: Note -> Note
crea n = pars n ^: "*"

-- Computability Regular expression
cre :: Note
cre = "E"

-- Computability Regexes over alphabet
creoa :: Note -> Note
creoa sigma = "RegEx" !: sigma

cres :: Note
cres = creoa calph

-- Computability Language of regular expression
clre :: Note -> Note
clre e = clan !: e

clore :: Note
clore = clre cre

-- Computability regular languages
creglan :: Note
creglan = "RegLan"


