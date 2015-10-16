module Macro.Math where

import           Macro.Index
import           Macro.MetaMacro
import           Macro.Text      (commaSeparated)
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

-- Sequences
sequ :: Note -> Note -> Note
sequ m n = pars m !: n


-- Comprehensions
compr :: Note -> Note -> Note -> Note -> Note
compr sign lower upper content = sign !: lower ^: upper <> braces content

comp :: Note -> Note -> Note -> Note
comp sign lower content = (braces $ sign !: (braces lower)) <> braces content


--[ Exam questions
examq :: Note -> Note -> Note
examq m n = do
  textbf $ "Exam Question: " <> m <> ", " <> n
  newline


--[ Sums

sumsign :: Note
sumsign = commS "sum"

sumcmp :: Note -> Note -> Note
sumcmp = comp sumsign

sumcmpr :: Note -> Note -> Note -> Note
sumcmpr = compr sumsign

-- Fraction
(/:) :: Note -> Note -> Note
(/:) = frac

-- Equality
eq :: Note -> Note -> Note
eq = between "="

neq :: Note -> Note -> Note
neq = between $ comm0 "neq"

(≠) :: Note -> Note -> Note
(≠) = neq

-- Inequality
lt :: Note -> Note -> Note
lt = between "<"

notsign :: Note
notsign = comm0 "neg"

not :: Note -> Note
not n = notsign <> n

(¬) :: Note -> Note
(¬) = not

-- Exponential
exp :: Note -> Note
exp n = "e" ^: n

--[ Symbols
bot :: Note
bot = comm0 "bot"

--[ Text
text :: Note -> Note
text = comm1 "text"

associative :: Note
associative = ix "associative"

commutative :: Note
commutative = ix "commutative"

idempotent :: Note
idempotent = ix "idempotent"

distributive :: Note
distributive = ix "distributive"

-- Proofs
np :: Note
np = do
  newline
  textit "no proof"
  newline

-- Tuples
tuple :: Note -> Note -> Note
tuple a b = pars $ commaSeparated [a, b]

triple :: Note -> Note -> Note -> Note
triple a b c = pars $ commaSeparated [a, b, c]

quadruple :: Note -> Note -> Note -> Note -> Note
quadruple a b c d = pars $ commaSeparated [a, b, c, d]

quintuple :: Note -> Note -> Note -> Note -> Note -> Note
quintuple a b c d e = pars $ commaSeparated [a, b, c, d, e]

-- Absolute value
av :: Note -> Note
av = autoBrackets "|" "|"

-- Bold math
bm :: Note -> Note
bm = comm1 "bm"
