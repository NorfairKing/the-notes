module Logic.Macro where

import           Macro.MetaMacro
import           Macro.Text
import           Types

-- Logic theory
logict :: Note
logict = mathbb "T"

-- Logic formula
logicf :: Note
logicf = "f"

-- Logic provable
lpvsign :: Note
lpvsign = comm0 "vdash"

lpv :: Note -> Note
lpv n = lpvsign <> n


-- Logical inference
linf :: [Note] -> Note -> Note
linf n m = comm2 "infer" m $ commaSeparated n
