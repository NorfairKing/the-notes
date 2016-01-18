module Functions.Jections where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Logic.PropositionalLogic.Macro

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms

import           Functions.Jections.Terms

jectionsS :: Note
jectionsS = section "Jections" $ do
    injectionDefinition
    todo "surjective and bijective"

injectionDefinition :: Note
injectionDefinition = de $ do
    lab injectionDefinitionLabel
    lab injectiveDefinitionLabel
    s ["A", function, m funfunc_, "is called an", injection', "or an", injective', function, "if the following holds"]
    let x = "x"
        y = "y"
    ma $ fa (x ∈ dom_) $ fa (y ∈ dom_) $ (x ≠ y) ⇒ (fn fun_ x ≠ fn fun_ y)
