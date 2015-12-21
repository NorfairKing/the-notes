module Macro.Theorem where

import           Types

import           Text.LaTeX.Packages.AMSThm (theorem)

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

newmdtheoremenv :: String -> Note -> Note
newmdtheoremenv nm n = do
    packageDep_ "mdframed"
    thm nm n
  where
    thm :: LaTeXC l => String -> l -> l
    thm name = liftL $ \l -> TeXComm "newmdtheoremenv" [ FixArg $ fromString name , OptArg "thm", FixArg l ]



