module Macro.Framed where

import           Types

framed :: Note -> Note
framed n = do
    comm1 "begin" "mdframed"
    n
    comm1 "end" "mdframed"
