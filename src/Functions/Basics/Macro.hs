module Functions.Basics.Macro where

import           Types

import           Macro.Math
import           Macro.MetaMacro

import           Functions.Application.Macro
import           Macro.Sets.CarthesianProduct
import qualified Relations.Domain.Macro       as R (dom, img)

-- * Functions
-- | Standard symbol for the underlying relation of a function
fun_ :: Note
fun_ = "f"

-- | Tuple notation of a function
funfunc :: Note -> Note -> Note -> Note
funfunc = triple

-- | Tuple notation with standard symbols
-- > funfunc_ = fun fun_ dom_ img_
funfunc_ :: Note
funfunc_ = fun fun_ dom_ img_

-- * Function definition

-- | Shorthand function definiton
fun :: Note -- ^ Name
    -> Note -- ^ Corange
    -> Note -- ^ Codomain
    -> Note
fun m n o = m <> negspace <> ":" <> raw "\\, " <> n <> rightarrow <> o
  where
    negspace :: Note
    negspace = commS "kern" <> raw "-2pt"

-- | Longhand function definition
func :: Note -- ^ Name
     -> Note -- ^ Corange
     -> Note -- ^ Codomain
     -> Note -- ^ Element
     -> Note -- ^ Image
     -> Note
func m n o p q = fun m n o <> ":" <> raw "\\ " <> p <> comm0 "mapsto" <> q

-- | Longhand function definition with set of tuples as corange
func2 :: Note -- ^ Name
      -> Note -- ^ Corange, part 1
      -> Note -- ^ Corange, part 2
      -> Note -- ^ Codomain
      -> Note -- ^ Element, part 1
      -> Note -- ^ Element, part 2
      -> Note -- ^ Image
      -> Note
func2  m n1 n2 o p1 p2 = func m (n1 ⨯ n2) o (tuple p1 p2)

-- * Domain

-- | Standard domain (or corange) symbol
dom_ :: Note
dom_ = "A"

-- | Domain of a function
dom :: Note -> Note
dom = R.dom

-- * Image

-- | Standard image (or codomain) symbol
img_ :: Note
img_ = "B"

-- | Image of a function
img :: Note -> Note
img = R.img


-- * Misc functions
-- | Arcsin
arcsin_ :: Note -> Note
arcsin_ = app arcsin

-- | Arccos
arccos_ :: Note -> Note
arccos_ = app arcsin


-- Binary Operations
funbinopsign :: Note
funbinopsign = comm0 "star"

funbinop :: Note -> Note -> Note
funbinop f a = fun (pars f) (a ⨯ a) a

funbinop_ :: Note
funbinop_ = funbinop funbinopsign dom_

funbinopapp :: Note -> Note -> Note
funbinopapp = binop funbinopsign

-- C-k 2*
(★) :: Note -> Note -> Note
(★) = funbinopapp

