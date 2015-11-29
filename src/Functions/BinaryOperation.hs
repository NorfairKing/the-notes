module Functions.BinaryOperation (
      binaryOperations

    , binaryOperation   , binaryOperation_

    , associative       , associative_
    ) where

import           Notes

import           Functions.Basics (binaryFunction)

makeDefs [
      "binary operation"
    , "associative"
    ]

binaryOperations :: Notes
binaryOperations = notesPart "binary-operations" body

body :: Note
body = do
    section "Binary operations"
    binaryOperationDefinition

    associativeDefinition

binaryOperationDefinition :: Note
binaryOperationDefinition = de $ do
    lab binaryOperationDefinitionLabel
    s ["A ", binaryOperation', " is a ", binaryFunction, " as follows"]
    ma $ fun funrel_ (fundom_ ⨯ fundom_) fundom_

associativeDefinition :: Note
associativeDefinition = de $ do
    lab associativeDefinitionLabel
    s ["A ", binaryOperation, " ", m funbinop_ , " is called ", associative', " if ", quoted "placement of parentheses does not matter"]
    ma $ fa (cs [a, b, c] ∈ fundom_) ((pars $ a ★ b) ★ c) =: (a ★ (pars $ b ★ c))

    exneeded
  where
    a = "a"
    b = "b"
    c = "c"


