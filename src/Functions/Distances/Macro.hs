module Functions.Distances.Macro where

import           Types

import           Macro.MetaMacro

import           Functions.Application.Macro

-- | Standard distance function symbol
dist_ :: Note
dist_ = "d"

-- | Standard metric symbol
metr_ :: Note
metr_ = dist_

-- | Application of given distance
distapp :: Note -> Note -> Note -> Note
distapp = app2

-- | Application of standard distance
-- > distapp_ = distapp dist_
distapp_ :: Note -> Note -> Note
distapp_ = distapp dist_

-- | Application of given metric
metrapp :: Note -> Note -> Note -> Note
metrapp = distapp

-- | Application of standard metric
metrapp_ :: Note -> Note -> Note
metrapp_ = metrapp metr_

-- * Norms

-- | N-norm of an element
norm_ :: Note -- ^ N
      -> Note -- ^ Element
      -> Note
norm_ n b = autoBrackets dblPipe dblPipe b !: n

norm :: Note -> Note
norm = norm_ ""
