module Relations.Preorders where

import           Notes

import           Relations.Basics.Terms

import           Relations.Preorders.Macro
import           Relations.Preorders.Terms

preorders :: Note
preorders = section "Preorders" $ do

    preorderDefinition

preorderDefinition :: Note
preorderDefinition = de $ do
    lab preorderDefinitionLabel
    s ["A ", relation, " ", m preord_, " between a set ", m xx, " and itself is called an ", preorder', " if it is ", reflexive_, and, transitive_]
  where xx = "X"










