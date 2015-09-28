module Macro.Math where

import           Macro.MetaMacro
import           Types

m :: Note -> Note
m = math

ma :: Note -> Note
ma = mathDisplay

pars :: Note -> Note
pars = autoParens

brac :: Note -> Note
brac = autoBraces

sqbrac :: Note -> Note
sqbrac = autoSquareBrackets

leftRightarrow :: Note
leftRightarrow = comm0 "Leftrightarrow"

leftrightarrow :: Note
leftrightarrow = comm0 "leftrightarrow"

leftarrow :: Note
leftarrow = comm0 "leftarrow"

leftArrow :: Note
leftArrow = comm0 "Leftarrow"

rightarrow :: Note
rightarrow = comm0 "rightarrow"

rightArrow :: Note
rightArrow = comm0 "Rightarrow"

mid :: Note
mid = comm0 "mid"

divSign :: Note
divSign = mid

mdiv :: Note -> Note -> Note
mdiv = binop divSign

defineasSign :: Note
defineasSign = quad <> comm0 "equiv" <> quad

defineas :: Note -> Note -> Note
defineas = binop defineasSign

(===) :: Note -> Note -> Note
(===) = defineas

forallSign :: Note
forallSign = comm0 "forall"

fa :: Note -> Note -> Note
fa n m = forallSign <> n <> ":" <> raw "\\ " <> m

dotsc :: Note
dotsc = comm0 "dotsc"

dotsb :: Note
dotsb = comm0 "dotsb"

overset :: Note -> Note -> Note
overset = comm2 "overset"

underset :: Note -> Note -> Note
underset = comm2 "underset"

-- Logic
mand :: Note -> Note -> Note
mand = wedge

(&:) :: Note -> Note -> Note
(&:) = mand

mor :: Note -> Note -> Note
mor = vee

(|:) :: Note -> Note -> Note
(|:) = mor

iffsign :: Note
iffsign = leftRightarrow

iff :: Note -> Note -> Note
iff m n = m <> iffsign <> n

-- C-k ==
(⇔) :: Note -> Note -> Note
(⇔) = iff

impliessign :: Note
impliessign = rightArrow

mimplies :: Note -> Note -> Note
mimplies m n = m <> impliessign <> n

-- C-k =>
(⇒) :: Note -> Note -> Note
(⇒) = mimplies

proof :: Note -> Note
proof = liftL $ TeXEnv "proof" []

subseteqsign :: Note
subseteqsign = comm0 "subseteq"

subseteq :: Note -> Note -> Note
subseteq m n = m <> subseteqsign <> n



-- Functions
fun :: Note -> Note -> Note -> Note
fun m n o = m <> ":" <> raw "\\ " <> n <> rightarrow <> o

func :: Note -> Note -> Note -> Note -> Note -> Note
func m n o p q = fun m n o <> ":" <> raw "\\ " <> p <> comm0 "mapsto" <> q

funinv :: Note -> Note
funinv n = n ^: (-1)

funapp :: Note -> Note -> Note
funapp n m = n <> pars m

-- Intervals
interval :: LaTeXC l => [TeXArg] -> l -> l -> l
interval args = liftL2 $ (\l1 l2 -> TeXComm "interval" (args ++ [FixArg l1, FixArg l2]))

ooint :: LaTeXC l => l -> l -> l
ooint = interval [OptArg "open"]

ocint :: LaTeXC l => l -> l -> l
ocint = interval [OptArg "open left"]

coint :: LaTeXC l => l -> l -> l
coint = interval [OptArg "open right"]

ccint :: LaTeXC l => l -> l -> l
ccint = interval []

-- Inequality
ge :: Note
ge = comm0 "geqslant"

le :: Note
le = comm0 "leqslant"


-- Sequences
seq :: Note -> Note -> Note
seq m n = brac m !: n


-- Comprehensions
compr :: Note -> Note -> Note -> Note -> Note
compr sign lower upper content = sign !: lower ^: upper <> braces content

comp :: Note -> Note -> Note -> Note
comp sign lower content = sign !: lower <> braces content
