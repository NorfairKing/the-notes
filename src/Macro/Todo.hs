module Macro.Todo where

import           Types

todo :: LaTeXC l => l -> l
todo = liftL $ \l -> TeXComm "todo" [MOptArg ["color=red", "inline", raw "size=\\small"], FixArg l ]

