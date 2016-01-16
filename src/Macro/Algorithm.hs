module Macro.Algorithm where

import           Types

import           Macro.Arrows
import           Macro.Math
import           Macro.MetaMacro

-- TODO when this is done with a renderer on a higher level, the line breaks need to be there automatically!
-- Also automatic math mode in the correct places!

renderAlgorithm :: Note -> Note
renderAlgorithm n = do
    raw "\n"
    packageDep_ "algorithm2e"
    liftL (TeXEnv "algorithm" [OptArg "H"]) n
    raw "\n"


-- | Asignment statement
assignS :: Note -> Note -> Note
assignS a b = binop (m leftarrow) (m a) (m b)

-- | Infix operator for assignment
(<-.) :: Note -> Note -> Note
(<-.) = assignS

-- | Ensure that I can omit most braces :D
infixr 0 <-.

-- | While statement
whileS :: Note -> Note -> Note
whileS a = comm2 "While" (m a)

-- | If statement
ifS :: Note -> Note -> Note
ifS a = comm2 "If" (m a)

-- | If - else statement
ifElseS :: Note -> Note -> Note -> Note
ifElseS a = comm3 "eIf" (m a)
