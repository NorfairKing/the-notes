module Macro.Figure where

import           Types

hereFigure :: LaTeXC l => l -> l
hereFigure = liftL $ \n -> TeXEnv "figure" [ OptArg $ TeXRaw "H" ] (comm0 "centering" <> n)

