module Logic.HoareLogic (hoareLogic) where

import           Notes

import           Logic.AbstractLogic (theory)

hoareLogic :: Notes
hoareLogic = notesPart "hoare-logic" body

body :: Note
body = do
  section "Hoare Logic"
  hoareLogicDefinition

p, a, q :: Note
p = "P"
a = "A"
q = "Q"

hoareLogicDefinition :: Note
hoareLogicDefinition = de $ do
  s [term "Hoare logic", " is a ", theory, "."]
  s ["In Hoare Logic, well-formed formulae are ", term "Hoare triple", "s."]
  ma $ htrip p a q
  s ["Here, ", m p, and, m q, " are assertions and ", m a, " is a sequence of instructions for an abstract machine."]
  s ["A true sencence in Hoare Logic describes the fact that the program ", m a, " will, started in any machine state satisfying ", m p, " will, if it terminates, yield a state satisfying ", m q, "."]

