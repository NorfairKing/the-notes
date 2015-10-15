module Macro.Todo where

import           Types

todo :: LaTeXC l => l -> l
todo = liftL $ \l -> TeXComm "todo" [MOptArg ["color=red", "inline", raw "size=\\small"], FixArg l ]

toprove :: Note
toprove = toprove_ mempty

toprove_ :: Note -> Note
toprove_ n = todo $ do
  n
  newline
  "There is a proof missing here. "
  "You can help improve these notes by sending a proof to the author."

noproof :: Note
noproof = todo $ footnotesize $ do
  "There is a proof missing here. "
  "There is a chance that the proof does not belong here but a reference to a proof is desired nonetheless. "
  "You can help improve these notes by sending a reference to a proof to the author. "

exneeded :: Note
exneeded = todo $ do
  "There is an example missing here. "
  "You can help improve these notes by sending an example to the author."

citneeded :: Note
citneeded = todo $ do
  "[Citation needed]"
