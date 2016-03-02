module Groups.Main where

import           Notes                           hiding (inverse)

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
    groupDefinition

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

groupDefinition :: Note
groupDefinition = de $ do
    lab groupDefinitionLabel
    lab inverseDefinitionLabel
    s ["A", monoid, m grp_, "is called a", group', "if every element has an", inverse', "with respect to the", identity, m gid_]
    let a = "a"
        ai = ginv a
    ma $ fa (a ∈ grps_) $ te (ai ∈ grps_) $ a ** ai =: gid_ =: ai ** a
