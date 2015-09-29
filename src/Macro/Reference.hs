module Macro.Reference where

import           Types

reference :: Note -> Note -> Note
reference thkind label = footnote $ "See " <> thkind <> " " <> ref label <> " on page " <> pageref label <> "."

deref :: Note -> Note
deref = reference "definition"

thmref :: Note -> Note
thmref = reference "theorem"

