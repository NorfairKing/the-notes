module FormalMethods.Macro where

import           Types

import           Macro.Arrows
import           Macro.MetaMacro
import           Macro.Tuple

import           Functions.Application.Macro
import           Relations.Equivalence.Macro

-- | Concrete signature
sig_ :: Note
sig_ = comm0 "Sigma"

-- | Concrete set of variables
vars_ :: Note
vars_ = mathcal "X"

-- | Term algebra
ta :: Note -> Note -> Note
ta s = fn $ mathcal "T" !: s

-- | Concrete defineTerm algebra
ta_ :: Note
ta_ = ta sig_ vars_

-- | Concrete set of equations
eqs_ :: Note
eqs_ = "E"

-- | Equational theory
et :: Note -> Note -> Note
et = tuple

-- | Concrete equational theory
et_ :: Note
et_ = et sig_ eqs_

-- | Right-oriented equations of a given set of equations
res :: Note -> Note
res = comm2 "overset" rightarrow

-- | Right-oriented equations of a given set of equations
les :: Note -> Note
les = comm2 "overset" leftarrow

-- | Right rule
rr :: Note -> Note -> Note
rr = binop rightarrow

-- | Left rule
lr :: Note -> Note -> Note
lr = binop leftarrow

-- * Cryptographic messages

-- | Set of agents
ags_ :: Note
ags_ = mathcal "A"

-- | Set of fresh values
frsh_ :: Note
frsh_ = mathcal "F"

-- | Set of user-defined functions
fncs_ :: Note
fncs_ = "Func"

-- | Pairing
pair :: Note -> Note -> Note
pair a b = autoAngleBrackets $ a <> ", " <> b

-- | Public key
pk :: Note -> Note
pk = fn "pk"

-- | Asymmetric encryption
aenc :: Note -> Note -> Note
aenc a b = autoBraces a !: b

-- | Assymmetric encryption (in words)
aenc_ :: Note -> Note -> Note
aenc_ = fn2 "aenc"

-- | Assymmetric decryption (in words)
adec_ :: Note -> Note -> Note
adec_ = fn2 "adec"

-- | Symmetric encryption
senc :: Note -> Note -> Note
senc a b = autoBraces (abs a) !: b

-- | Symmetric encryption (in words)
senc_ :: Note -> Note -> Note
senc_ = fn2 "senc"

-- | Symmetric decryption (in words)
sdec_ :: Note -> Note -> Note
sdec_ = fn2 "sdec"

-- | Syntactic equality
synteq :: Note -> Note -> Note
synteq = binop $ "=" !: "syntactic"

(=!=) :: Note -> Note -> Note
(=!=) = synteq

-- | Equality in equation set
eqr :: Note -> Note
eqr sub = "=" !: sub

eq :: Note -> Note -> Note -> Note
eq sub = ineqrel $ eqr sub

eqr_ :: Note
eqr_ = eqr eqs_

eq_ :: Note -> Note -> Note
eq_ = eq eqs_

-- | Concrete Substitution function
subs_ :: Note
subs_ = sigma

-- | Apply a given sustitution
apsub :: Note -- ^ Substitution
      -> Note -- ^ An element
      -> Note
apsub sub n = n <> sub

-- | Like @apsub@ but shorter, in the same spirit as @fn@.
sb :: Note -> Note -> Note
sb = apsub

-- | Application of the standard substitution: @subs_@
sb_ :: Note -> Note
sb_ = sb subs_

-- Concrete position
pos_ :: Note
pos_ = "p"

-- | Subterm selection
subt :: Note -- ^ Term
     -> Note -- ^ Position
     -> Note
subt term pos = term <> "|" !: pos

(|.) :: Note -> Note -> Note
(|.) = subt


-- | Subterm replacement
trepl :: Note -- ^ Term
      -> Note -- ^ Replacement
      -> Note -- ^ Position
      -> Note
trepl t r p = t <> autoSquareBrackets r !: p


-- | Question mark above equation
qeq :: Note -> Note -> Note
qeq = binop $ comm2 "overset" "?" "="

-- | Infix version of the above
--
-- TODO move this to the math macros?
(=?=) :: Note -> Note -> Note
(=?=) = qeq
