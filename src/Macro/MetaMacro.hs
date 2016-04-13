module Macro.MetaMacro where

import           Types

defineEnvironment :: String -> Note -> Note
defineEnvironment name = liftL $ TeXEnv name []

comm2 :: LaTeXC l => String -> l -> l -> l
comm2 name = liftL2 $ \l1 l2 -> TeXComm name [FixArg l1, FixArg l2]

comm3 :: LaTeXC l => String -> l -> l -> l -> l
comm3 name = liftL3 $ \l1 l2 l3 -> TeXComm name [FixArg l1, FixArg l2, FixArg l3]

renewcommand :: LaTeXC l => String -> l -> l
renewcommand l = comm2 "renewcommand" $ commS l

renewcommand1 :: LaTeXC l => l -> l -> l
renewcommand1 = liftL2 $ \l1 l2 -> TeXComm "renewcommand" [FixArg $ raw "\\" <> l1, OptArg "1", FixArg l2]

-- Binary operation
binop :: Note -> Note -> Note -> Note
binop = between

-- * Subscript

-- | Safe Subscript
(!:) :: Note -> Note -> Note
x !: y = braces x <> raw "_" <> braces y

-- | Prefix Subscript Operator
subsc :: Note -> Note -> Note
subsc = (!:)

-- | Unsafe (in the first argument) Subscript.
(.!:) :: LaTeXC l => l -> l -> l
x .!: y = x <> raw "_" <> braces y


-- * Superscript

-- | Superscript
(^:) :: Note -> Note -> Note
x ^: y = braces x <> raw "^"  <> braces y

-- | Prefix Superscript Operator
supsc :: Note -> Note -> Note
supsc = (^:)

-- | Unsafe (in the first argument) Superscript.
(.^:) :: LaTeXC l => l -> l -> l
x .^: y = x <> raw "^"  <> braces y



-- * Comprehensions
compr :: Note -> Note -> Note -> Note -> Note
compr sign lower upper content = sign .!: lower .^: upper <> braces content

comp :: Note -> Note -> Note -> Note
comp sign lower content = braces (sign .!: braces lower) <> braces content

