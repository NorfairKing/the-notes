module Macro.Math where

import           Types

import qualified Prelude         as P

import           Macro.Arrows
import           Macro.MetaMacro
import           Macro.Text      (commaSeparated)


m :: LaTeXC l => l -> l
m = math

ma :: LaTeXC l => l -> l
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

div :: Note -> Note -> Note
div = binop divSign

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
interval args = liftL2 $ (\l1 l2 -> TeXComm "interval" (args P.++ [FixArg l1, FixArg l2]))

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
argmax :: Note -> Note -> Note
argmax arg body = underset arg ("arg" <> commS "!" <> commS "max") <> commS " " <> body

argmin :: Note -> Note -> Note
argmin arg body = underset arg ("arg" <> commS "!" <> commS "min") <> commS " " <> body

-- Infinity
minfty :: Note
minfty = "-" <> infty

pinfty :: Note
pinfty = "+" <> infty

-- Limits
lim :: Note -> Note -> Note -> Note
lim m n o = (commS "lim" .!: (m → n)) <> o

lim2 :: Note -> Note -> Note -> Note -> Note -> Note
lim2 a x b y c = (commS "lim" .!: (commaSeparated [a → x, b → y])) <> c

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

-- * Integrals
int :: Note -> Note -> Note -> Note -> Note
int a b c dx = commS "int" .!: a .^: b <> c <> commS "," <> "d" <> dx

int_ :: Note -> Note -> Note -> Note
int_ a = int a ""

-- | Cases
cases :: LaTeXC l => l -> l
cases = liftL $ TeXEnv "cases" []

-- | Lists
lst :: Note -> Note -> Note
lst n m = commaSeparated [n, dotsc, m]

list :: Note -> Note -> Note -> Note
list n m o = commaSeparated [n, m, dotsc, o]

-- | Combination
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

-- | Nicely aligned equalities
aligns :: (Note -> Note -> Note) -> Note -> [Note] -> Note
aligns _ f [] = f
aligns eq f (r:rs) = align_ $ (f & eq "" r) : P.map (\n -> "" & eq "" n) rs

aligneqs :: Note -> [Note] -> Note
aligneqs = aligns (=:)


-- | Cancel out an expression
cancel :: Note -> Note
cancel n = do
    packageDep_ "cancel"
    comm1 "cancel" n


-- * Partial derivatives
partial' :: Note
partial' = comm0 "partial"

-- | Shorthand partial derivative
partd :: Note -> Note -> Note
partd a b = (partial' <> a) /: (partial' <> b)

-- | Longhand partial derivative
partiald :: Note -> Note -> Note
partiald a b = (partial' /: (partial' <> b)) <> a




-- * Math font
mathfrak :: Note -> Note
mathfrak n = do
    packageDep_ "eufrak"
    comm1 "mathfrak" n


-- * Logarithms

log :: Note -> Note
log n = commS "log" <> n

logn :: Note -> Note -> Note
logn n m = commS "log" !: n <> m

-- * Cdot

cdot_ :: Note
cdot_ = comm0 "cdot"

-- * Standard operations
(<=) :: Note -> Note -> Note
(<=) = (<=:)

(>=) :: Note -> Note -> Note
(>=) = (>=:)

(>) :: Note -> Note -> Note
(>) = (>:)

(<) :: Note -> Note -> Note
(<) = (<:)

(^) :: Note -> Note -> Note
(^) = (^:)


-- | Underscore (as in, ignoring this argument)
unmatched :: Note
unmatched = comm1 "text" "_"
