module Groups.Main where

import           Notes

import           Functions.Basics.Macro
import           Functions.BinaryOperation.Terms
import           Logic.FirstOrderLogic.Macro
import           Sets.Basics.Terms

import           Groups.Macro
import           Groups.Terms

groups :: Note
groups = chapter "Groups" $ do
    magmaDefinition
    semigroupDefinition
    monoidDefinition

magmaDefinition :: Note
magmaDefinition = de $ do
    lab magmaDefinitionLabel
    s ["A", magma', m mgm_, "is a", set <> ", equipped with a", binaryOperation]
    ma $ fun2 (pars $ "" · "") mgms_ mgms_ mgms_

semigroupDefinition :: Note
semigroupDefinition = de $ do
    lab semigroupDefinitionLabel
    s ["A", magma, m sgrp_, "is called a", semigroup', "if its operation", m $ "" ˙ "", "is", associative_]

monoidDefinition :: Note
monoidDefinition = de $ do
    lab monoidDefinitionLabel
    lab identityDefinitionLabel
    s ["A", semigroup, m mnd_, "is called a", monoid', "if it has an", identity, m mid_]
    let a = "a"
    ma $ fa (a ∈ mnds_) $ a ˚ mid_ =: a =: mid_ ˚ a
