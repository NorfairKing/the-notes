module Relations.Preorders where

import           Notes

import           Relations.Basics          (reflexive_, relation, transitive_)

import           Relations.Preorders.Macro

makeDefs [
      "preorder"
    ]

preorders :: Note
preorders = note "preorders" $ do
  section "Preorders"

  preorderDefinition

preorderDefinition :: Note
preorderDefinition = de $ do
    lab preorderDefinitionLabel
    s ["A ", relation, " ", m preord_, " between a set ", m xx, " and itself is called an ", preorder', " if it is ", reflexive_, and, transitive_]
  where xx = "X"










