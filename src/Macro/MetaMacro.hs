module Macro.MetaMacro where

import           Types

environment :: String -> (Note -> Note)
environment name = liftL $ TeXEnv name []

comm2 :: LaTeXC l => String -> l -> l -> l
comm2 name = liftL2 $ (\l1 l2 -> TeXComm name [FixArg l1, FixArg l2])

comm3 :: LaTeXC l => String -> l -> l -> l -> l
comm3 name = liftL3 $ (\l1 l2 l3 -> TeXComm name [FixArg l1, FixArg l2, FixArg l3])

renewcommand :: LaTeXC l => l -> l -> l
renewcommand l = comm2 "renewcommand" (raw "\\" <> l)

renewcommand1 :: LaTeXC l => l -> l -> l
renewcommand1 = liftL2 $ (\l1 l2 -> TeXComm "renewcommand" [FixArg $ raw "\\" <> l1, OptArg "1", FixArg l2])

-- Binary operation
binop :: Note -> Note -> Note -> Note
binop = between


-- prefix subscript operator
subsc :: Note -> Note -> Note
subsc = (!:)

-- prefix superscript operator
supsc :: Note -> Note -> Note
supsc = (^:)


-- | Special Superscript.
(.^:) :: LaTeXC l => l -> l -> l
x .^: y = x <> raw "^"  <> braces y


-- | Special Subscript.
(.!:) :: LaTeXC l => l -> l -> l
x .!: y = x <> raw "_" <> braces y

-- Comprehensions
compr :: Note -> Note -> Note -> Note -> Note
compr sign lower upper content = sign .!: lower .^: upper <> braces content

comp :: Note -> Note -> Note -> Note
comp sign lower content = (braces $ sign .!: (braces lower)) <> braces content

