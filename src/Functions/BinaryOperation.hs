module Functions.BinaryOperation where

import           Notes

import           Logic.FirstOrderLogic.Macro
import           Sets.Basics.Terms

import           Functions.Basics.Macro
import           Functions.Basics.Terms

import           Functions.BinaryOperation.Macro
import           Functions.BinaryOperation.Terms

binaryOperations :: Note
binaryOperations = section "Binary operations" $ do
    todo "binary operations x ⨯ y -> z"
    binaryOperationDefinition

    associativeDefinition
    todo "Left identity and right identity"
    identityDefinition
    identityUniqueTheorem
    identityExamples

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


identityDefinition :: Note
identityDefinition = de $ do
    let x = "X"
    s ["Let", m x, "be a", set, and, m binop_, "a", binaryOperation, "on", m x]
    s ["If", m x, "contains an", element, m bid_, "with the following property, that element is called an", identity', or, neutralElement']
    let a = "a"
    ma $ fa (a ∈ x) $ a ★ bid_ =: bid_ =: bid_ ★ a

identityUniqueTheorem :: Note
identityUniqueTheorem = thm $ do
    lab identityUniqueTheoremLabel
    let a = "A"
    s ["If there exists an", identity, "for a", binaryOperation, m binop_, "in a", set, m a, "then it must be unique"]

    proof $ do
        let e = "e"
            f = "f"
        s ["Let", m e, and, m f, "be two", identities, "in", m a]
        ma $ e =: e ★ f =: f
        s ["Note that the first equation uses that", m f, "is an", identity, "and the second equation that", m e, "is an", identity]

identityExamples :: Note
identityExamples = do
    exneeded
