module Macro (
    module Macro
  , module Macro.Index
  , module Macro.Math
  , module Macro.MetaMacro
  , module Macro.Section
  , module Macro.Text
  , module Macro.Theorem
  , module Sets.Macro
  ) where

import           Macro.Index
import           Macro.Math
import           Macro.MetaMacro
import           Macro.Section
import           Macro.Text
import           Macro.Theorem
import           Sets.Macro
import           Types

quoted :: Note -> Note
quoted n = "`" <> n <> "'"

