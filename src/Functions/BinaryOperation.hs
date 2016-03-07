module Functions.BinaryOperation where

import           Notes

import           Logic.FirstOrderLogic.Macro

import           Functions.Basics.Macro
import           Functions.Basics.Terms

import           Functions.BinaryOperation.Macro
import           Functions.BinaryOperation.Terms

binaryOperations :: Note
binaryOperations = section "Binary operations" $ do
    binaryOperationDefinition

    associativeDefinition

-- TODO(binary operation can go to other set than dom_
binaryOperationDefinition :: Note
binaryOperationDefinition = de $ do
    lab binaryOperationDefinitionLabel
    s ["A ", binaryOperation', " is a ", binaryFunction, " as follows"]
    ma $ fun fun_ (dom_ ⨯ dom_) dom_

associativeDefinition :: Note
associativeDefinition = de $ do
    lab associativeDefinitionLabel
    s ["A ", binaryOperation, " ", m binop_ , " is called ", associative', " if ", quoted "placement of parentheses does not matter"]
    ma $ fa (cs [a, b, c] ∈ dom_) ((pars $ a ★ b) ★ c) =: (a ★ (pars $ b ★ c))

    exneeded
  where
    a = "a"
    b = "b"
    c = "c"


