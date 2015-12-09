module Macro.Figure where

import           Types

hereFigure :: LaTeXC l => l -> l
hereFigure = liftL $ \n -> TeXEnv "figure" [ OptArg $ TeXRaw "H" ] (comm0 "centering" <> n)


pageFigure :: LaTeXC l => l -> l
pageFigure = liftL $ \n -> TeXEnv "figure" [ OptArg $ TeXRaw "!p" ] (comm0 "centering" <> n)

sidewaysFigure :: LaTeXC l => l -> l
sidewaysFigure = liftL $ \n -> TeXEnv "sidewaysfigure" [OptArg $ TeXRaw "!p"] (comm0 "centering" <> n)
