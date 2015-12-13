module Macro.Figure where

import           Types

import           Packages


hereFigure :: Note -> Note
hereFigure n = do
    packageDep_ "float"
    fig n
  where
    fig = liftL $ \n -> TeXEnv "figure" [ OptArg $ TeXRaw "H" ] (comm0 "centering" <> n)


pageFigure :: LaTeXC l => l -> l
pageFigure = liftL $ \n -> TeXEnv "figure" [ OptArg $ TeXRaw "!p" ] (comm0 "centering" <> n)

sidewaysFigure :: Note -> Note
sidewaysFigure n = do
    packageDep_ "rotating"
    fig n
  where
    fig = liftL $ \n -> TeXEnv "sidewaysfigure" [OptArg $ TeXRaw "!p"] (comm0 "centering" <> n)
