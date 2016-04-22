module Functions.Order.Macro where

import           Functions.Application.Macro (fn)
import           Macro.Math
import           Macro.MetaMacro
import           Types

-- * Conjunctive order

cordsign :: Note -> Note
cordsign = overset bullet

cord :: Note -- ^ The order sign
     -> Note
     -> Note
     -> Note
cord o = binop $ cordsign o

(<=-) :: Note -> Note -> Note
(<=-) = cord $ comm0 "leqslant"


-- * Regions

-- | Fixed point region
fix :: Note -> Note
fix = fn "Fix"

-- | Ascending region
asc :: Note -> Note
asc = fn "Asc"

-- | Descending region
desc :: Note -> Note
desc = fn "Desc"

-- * Extreme fixed points

-- | Least fixed point
lfp :: Note -> Note
lfp = fn "lfp"

-- | Greatest fixed point
gfp :: Note -> Note
gfp = fn "gfp"

-- * Kleene

-- | Kleene chain
kleeneCh :: Note -> Note
kleeneCh = fn "K"


-- * Galois connections

-- | A galois connection
gcon :: Note -- ^ bottom function
     -> Note -- ^ top function
     -> Note -- ^ 'from' lattice
     -> Note -- ^ 'to' lattice
     -> Note
gcon b t from to = do
    packageDep_ "galois"
    binop (comm2 "galois" b t) from to

-- | A galois insertion
gins :: Note -- ^ bottom function
     -> Note -- ^ top function
     -> Note -- ^ 'from' lattice
     -> Note -- ^ 'to' lattice
     -> Note
gins b t from to = do
    packageDep_ "galois"
    binop (comm2 "galoiS" b t) from to
