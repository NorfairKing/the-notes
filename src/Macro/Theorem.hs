module Macro.Theorem where

import           Types

de :: Note -> Note
de = theorem "de"

thm :: Note -> Note
thm = theorem "thm"

nte :: Note -> Note
nte = theorem "nte"

ex :: Note -> Note
ex = theorem "ex"

cex :: Note -> Note
cex = theorem "cex"

con :: Note -> Note
con = theorem "con"

prop :: Note -> Note
prop = theorem "prop"


newtheorem' :: LaTeXC l => String -> l -> l
newtheorem' name = liftL $ \l -> TeXComm "newtheorem" [ FixArg $ fromString name , OptArg "thm", FixArg l ]

newmdtheoremenv :: LaTeXC l => String -> l -> l
newmdtheoremenv name = liftL $ \l -> TeXComm "newmdtheoremenv" [ FixArg $ fromString name , OptArg "thm", FixArg l ]

