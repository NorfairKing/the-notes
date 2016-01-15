module Macro.Tikz where

import           Types

tikzpicture :: [Note] -> Note -> Note
tikzpicture args l = do
    raw "\n"
    packageDep_ "tikz"
    liftListL (\(l:args) -> TeXEnv "tikzpicture" [MOptArg args] l) (l:args)
    raw "\n"

axis :: [Note] -> Note -> Note
axis args l = do
    packageDep_ "pgfplots"
    liftListL (\(l:args) -> TeXEnv "axis" [MOptArg args] l) (l:args)

addPlot :: [Note] -> Note -> Note
addPlot args l = (<> ";") $ (liftListL $ \(l:args) -> TeXComm "addplot" [MOptArg args, FixArg l]) (l:args)

(=-) :: Note -> Note -> Note
(=-) = liftL2 $ \a b -> a <> "=" <> b




