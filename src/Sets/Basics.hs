module Sets.Basics (basics) where

import           Notes

basics :: Notes
basics = notesPart "basics" preamble body

preamble :: Note
preamble = return ()

body :: Note
body = do
  setDefinition

setDefinitionLabel :: Note
setDefinitionLabel = "de:set"

setDefinition :: Note
setDefinition = do
  label setDefinitionLabel
  de $ do
    "A "
    term "set"
    " is a "
    ix "collection"
    " of distint objects, considered as an object in its own right."
    " These objects are called the "
    term "elements"
    " of the set"

