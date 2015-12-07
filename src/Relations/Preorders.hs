module Relations.Preorders where

import           Notes

import           Relations.BasicDefinitions (reflexive_, relation, transitive_)

-- import           Relations.Preorders.Macro

makeDefs [
      "preorder"
    ]

preorders :: Notes
preorders = notesPart "preorders" $ do
  section "Preorders"

  preorderDefinition

preorderDefinition :: Note
preorderDefinition = de $ do
    lab preorderDefinitionLabel
    s ["A ", relation, " ", m rel, " between a set ", m xx, " and itself is called an ", preorder', " if it is ", reflexive_, and, transitive_]
  where xx = "X"










