module Functions.Inverse where

import           Notes                       hiding (inverse)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.Jections.Terms

import           Functions.Inverse.Macro
import           Functions.Inverse.Terms

inverseS :: Note
inverseS = section "Inverse" $ do
    inverseFunctionDefinition

inverseFunctionDefinition :: Note
inverseFunctionDefinition = de $ do
    lab inverseDefinitionLabel
    lab inverseFunctionDefinitionLabel
    s ["Let", m funfunc_, "be an", injective, function]
    s [the, inverse', m $ inv fun_, "of", m fun_, "is defined as follows"]
    let x = "x"
    ma $ func (inv fun_) img_ dom_ x $ fn (inv fun_) x
    s ["Here", m $ fn (inv fun_) x, "is the element that satisfies the following equation"]
    ma $ fn fun_ (fn (inv fun_) x) =: x
    s ["Because", m fun_, "is", injective, ", there exists at most one such element for any", m x, "and the inverse is therefore well-defined"]
