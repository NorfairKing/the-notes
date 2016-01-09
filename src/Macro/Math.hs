module Macro.Math where

import           Types

import           Macro.Arrows
import           Macro.Index
import           Macro.MetaMacro
import           Macro.Text      (commaSeparated)

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

mod :: Note -> Note -> Note
mod = between $ text " mod "

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


--[ Exam questions
examq :: Note -> Note -> Note -> Note
examq s m n = do
    textbf $ "Exam Question: " <> m <> " @ " <> s <> ", " <> n
    newline


--[ Sums

sumsign :: Note
sumsign = commS "sum"

sumcmp :: Note -> Note -> Note
sumcmp = comp sumsign

sumcmpr :: Note -> Note -> Note -> Note
sumcmpr = compr sumsign


-- Products

prodsign :: Note
prodsign = commS "prod"

prodcmp :: Note -> Note -> Note
prodcmp = comp prodsign

prodcmpr :: Note -> Note -> Note -> Note
prodcmpr = compr prodsign


-- Fraction
(/:) :: Note -> Note -> Note
(/:) = frac

-- Equality
eqsign :: Note
eqsign = "="

eq :: Note -> Note -> Note
eq = binop eqsign

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

--[ Text
text :: Note -> Note
text = comm1 "text"

commutative :: Note
commutative = ix "commutative"

idempotent :: Note
idempotent = ix "idempotent"

distributive :: Note
distributive = ix "distributive"

sequence :: Note
sequence = ix "sequence"

finite :: Note
finite = ix "finite"

infinite :: Note
infinite = ix "infinite"

differentiable :: Note
differentiable = ix "differentiable"

localMinimum :: Note
localMinimum = ix "local minimum"

localMaximum :: Note
localMaximum = ix "local maximum"

mean :: Note
mean = ix "mean"


-- Proofs
proof :: Note -> Note
proof = liftL $ TeXEnv "proof" []

np :: Note
np = do
    noindent
    textit "no proof"


-- Absolute value
av :: Note -> Note
av = autoBrackets "|" "|"

-- Bold math
bm :: Note -> Note
bm n = do
    packageDep_ "bm"
    comm1 "bm" n

-- Roots
sqrt :: Note -> Note
sqrt = tsqrt Nothing

nrt :: Note -> Note -> Note
nrt n = tsqrt (Just n)

-- * Extrema
-- | Maximum accross value
max :: Note -> Note -> Note
max sub body = commS "max" .!: sub <> body

-- | Maximum of
maxof :: Note -> Note
maxof body = commS "max" <> body

-- | Minimum accross value
min :: Note -> Note -> Note
min sub body = commS "min" .!: sub <> body

-- | Minimum of
minof :: Note -> Note
minof body = commS "min" <> body

-- | Arguments at minumum
argmin :: Note -> Note -> Note
argmin arg body = underset arg ("arg" <> commS "," <> commS "min") <> body

-- Infinity
minfty :: Note
minfty = "-" <> infty

pinfty :: Note
pinfty = "+" <> infty

-- Limits
lim :: Note -> Note -> Note -> Note
lim m n o = (commS "lim" !: (m → n)) <> o

-- C-k ->
(→) :: Note -> Note ->Note
(→) = binop rightarrow

rlim :: Note -> Note -> Note -> Note
rlim m n o = (commS "lim" !: (m <> overset ">" rightarrow) <> n) <> o

llim :: Note -> Note -> Note -> Note
llim m n o = (commS "lim" !: (m <> overset "<" rightarrow) <> n) <> o

-- Derivatives
deriv :: Note -> Note -> Note
deriv top to = ("d" <> commS ";" <> top) /: ("d" <> to)

-- Integrals
int :: Note -> Note -> Note -> Note -> Note
int a b c dx = commS "int" !: a ^: b <> c <> commS "," <> dx

-- Cases
-- | Environment of unordered lists. Use 'item' to start each list item.
cases :: LaTeXC l => l -> l
cases = liftL $ TeXEnv "cases" []

-- Lists
lst :: Note -> Note -> Note
lst n m = commaSeparated [n, dotsc, m]

list :: Note -> Note -> Note -> Note
list n m o = commaSeparated [n, m, dotsc, o]

-- Combinatorics
choose :: Note -> Note -> Note
choose = comm2 "binom"

-- | Pi
pi :: Note
pi = comm0 "pi"

-- | Sign
sign :: Note -> Note
sign n = "sign" <> autoParens n

-- | Plus-or-minus
pm :: Note -> Note
pm n = comm0 "pm" <> n

-- | Plus-or-minus
mp :: Note -> Note
mp n = comm0 "mp" <> n

-- | Gradient
grad :: Note -> Note
grad n = comm0 "nabla" <> n

-- | Partial derivative
partial :: Note -> Note
partial n = comm0 "partial" <> n
