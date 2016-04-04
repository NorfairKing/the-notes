module Macro.Arrows where

import           Types

import           TH.Command

comm 0 "leftrightarrow"
comm_ 0 "Leftrightarrow" "leftRightarrow"

comm 0 "leftarrow"
comm_ 0 "Leftarrow" "leftArrow"

comm 0 "rightarrow"
comm_ 0 "Rightarrow" "rightArrow"

comm 0 "longleftarrow"
comm 0 "longrightarrow"
