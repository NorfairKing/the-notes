module Functions.Basics.Macro where

import qualified Prelude                     as P (map)
import           Types

import           Macro.Arrows
import           Macro.MetaMacro
import           Macro.Sets.Macro
import           Macro.Tuple

import           Functions.Application.Macro
import qualified Relations.Domain.Macro      as R (dom, img)

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

-- | Function type
funt :: Note -> Note -> Note
funt a b = a <> rightarrow <> b

-- * Function definition

-- | Shorthand function definiton
fun :: Note -- ^ Name
    -> Note -- ^ Corange
    -> Note -- ^ Codomain
    -> Note
fun m n o = m <> negspace <> ":" <> raw "\\, " <> funt n o
  where
    negspace :: Note
    negspace = commS "kern" <> raw "-2pt"

-- | Shorthand function definition
fun2 :: Note -- ^ Name
     -> Note -- ^ Corange, part 1
     -> Note -- ^ Corange, part 2
     -> Note -- ^ Codomain
     -> Note
fun2 m n1 n2 = fun m (n1 ⨯ n2)

-- | Shorthand function definition
fun3 :: Note -- ^ Name
     -> Note -- ^ Corange, part 1
     -> Note -- ^ Corange, part 2
     -> Note -- ^ Corange, part 3
     -> Note -- ^ Codomain
     -> Note
fun3 m n1 n2 n3 = fun m (n1 ⨯ n2 ⨯ n3)

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
func2 m n1 n2 o p1 p2 = func m (n1 ⨯ n2) o (tuple p1 p2)

-- * Function comprehension
funcomp :: [(Note, Note)] -> Note
funcomp tups = setofs $ P.map (\(a,b) -> a <> mapsto <> b) tups

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

-- | The unit function for a given domain
unitf :: Note -> Note
unitf = (unitf_ !:)

-- | A general unit function
unitf_ :: Note
unitf_ = mathcal "U"


-- * Misc functions
-- | Arcsin
arcsin_ :: Note -> Note
arcsin_ = app arcsin

-- | Arccos
arccos_ :: Note -> Note
arccos_ = app arcsin

