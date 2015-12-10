module Logic.SeparationLogic where

import           Notes

import           Logic.AbstractLogic
import           Logic.HoareLogic.Macro      hiding (satis)
import           Logic.HoareLogic.Terms      hiding (satisfies, satisfies')
import           Logic.SeparationLogic.Macro
import           Logic.SeparationLogic.Terms

separationLogicS :: Notes
separationLogicS = notesPart "separation-logic" $ do
    section "Separation Logic"

    heapDefinition

    separationLogicDefinition

    satisfiesDefinition

    emptyHeapSemanticsDefinition
    pointsToSemanticsDefinition
    separatingConjunctionSemanticsDefinition
    chainedPointsToDefinition
    separatingImplicationSemanticsDefinition

    satisfactionExamples

    fetchAssignmentDefinition
    heapMutationDefinition
    allocationAssignmentDefinition
    disposalDefinition

    separationLogicAxioms

    tripleInterpretiation


heapDefinition :: Note
heapDefinition = de $ do
    lab heapDefinitionLabel
    s ["A ", heap', " is a partial function from a set of locations (pointers) to values"]
    s ["The difference between a ", heap, " and a program state is that values on the heap can represent other locations on the heap"]
    s ["In this new model, variables will evaluate to locations"]
    s [the, heap, " will then tell us what the value is that is stored at that location"]


separationLogicDefinition :: Note
separationLogicDefinition = de $ do
    lab separationLogicDefinitionLabel
    s [separationLogic', " is an extension to ", hoareLogic_, " that facilitates local reasoning"]
    s [separationLogic, " offers spatial connectives that allow for more modular reasoning"]
    s ["In ", separationLogic, " program states comprise of both a variable store and a heap"]


satisfiesDefinition :: Note
satisfiesDefinition = de $ do
    s ["Assertion satisfaction needs to be redefined in ", separationLogic, " to incorporate the heap"]
    s ["The expression that represents ", dquoted $ s ["A program state ", m st, ", together with a heap ", m hp, ", ", satisfies', " an ", assertion, " ", m p], " is denoted as ",  m $ satis "s" "h" "P"]
    s ["It is inductively defined as follows"]
    itemize $ do
        item $ s [m $ ss false, " never holds"]
        item $ s [m $ ss true, " always holds"]
        item $ m $ ss (p ∧ q) ⇔ (ss p ∧ ss q)
        item $ m $ ss (p ∨ q) ⇔ (ss p ∨ ss q)
        item $ m $ ss (p ⇒ q) ⇔ (ss p ⇒ ss q)
        item $ m $ ss (e =: f) ⇔ (e .: st =: f .: st)
  where
    ss = satis st hp
    st = "s"
    hp = "h"
    p = "P"
    q = "Q"
    e = "e"
    f = "f"

emptyHeapSemanticsDefinition :: Note
emptyHeapSemanticsDefinition = de $ do
    s [m emp, " represents the assertion that the heap is empty"]
    m $ ss emp ⇔ (hp =§= emptyset)
    exneeded
  where
    ss = satis st hp
    st = "s"
    hp = "h"


pointsToSemanticsDefinition :: Note
pointsToSemanticsDefinition = de $ do
    lab pointsToDefinitionLabel
    m $ ss (e .-> f) ⇔ hp =§= ((e .: st) .-> (f .: st)) ∈ hp
    s ["... or informally: ", dquoted $ s ["There exists a value ", m f, " on the heap that ", m e, " (which may also be a value on the heap) points to and no others"]]
    exneeded
  where
    ss = satis st hp
    st = "s"
    hp = "h"
    e = "e"
    f = "f"


separatingConjunctionSemanticsDefinition :: Note
separatingConjunctionSemanticsDefinition = de $ do
    m $ ss (p -* q) ⇔ (te (cs [h1, h2]) $ between (comm0 "bot") h1 h2 ∧ between (comm0 "circ") h1 h2 =: hp ∧ satis st h1 p ∧ satis st h2 q)
    s ["... or informally: ", dquoted $ s ["The heap can be divided into two parts ", m h1, and, m h2, ", one where ", m $ satis st h1 p, " holds and one where ", m $ satis st h2 q]]
    exneeded
  where
    ss = satis st hp
    st = "s"
    hp = "h"
    h1 = hp !: 1
    h2 = hp !: 2
    p = "P"
    q = "Q"

chainedPointsToDefinition :: Note
chainedPointsToDefinition = de $ do
    s ["The notation ", m $ e ..-> [f0, f1, dotsc, fn], " is a shorthand for the following"]
    ma $ (e .-> f0) .* (e + 1 .-> f1) .* dotsc .* ((e + n) .-> fn)
    exneeded
  where
    e = "e"
    f = "f"
    n = "n"
    f0 = f !: 0
    f1 = f !: 1
    fn = f !: n

separatingImplicationSemanticsDefinition :: Note
separatingImplicationSemanticsDefinition = de $ do
    s [m $ satis st hp (p -* q), " is said to hold if and only if ", dquoted $ s ["Extending ", m hp, " with a disjoint part ", m hp', " that satisfies ", m p, " results in a new heap satisfying ", m q]]
    exneeded
  where
    hp = "h"
    hp' = "h'"
    st = "s"
    p = "P"
    q = "Q"

satisfactionExamples :: Note
satisfactionExamples = todo "examples on slide 43"

fetchAssignmentDefinition :: Note
fetchAssignmentDefinition = de $ do
    s [m $ e .& hp, " represents the location of the variabl that is said to be stored in ", m e]
    exneeded
  where
    hp = "h"
    e = "e"

heapMutationDefinition :: Note
heapMutationDefinition = de $ do
    s [m $ (e .& hp) =:= f, " represents the instruction to assign the value of ", m f, " as the contents of ", m (e .& hp), " on the heap"]
  where
    hp = "h"
    e = "e"
    f = "f"

allocationAssignmentDefinition :: Note
allocationAssignmentDefinition = de $ do
    s [m $ cons [e1, dotsc, en], " represents the instruction to allocate ", m n, " consecutive locations that are not in the heap yet, say ", m $ cs [l1, dotsc, ln], " and assign the values of ", m $ cs [e1, dotsc, en], " to the contents of ", m $ cs [l1, dotsc, ln], " respectively"]
    exneeded
  where
    e = "e"
    e1 = e !: 1
    en = e !: n
    l = "l"
    l1 = l !: 1
    ln = l !: n
    n = "n"

disposalDefinition :: Note
disposalDefinition = de $ do
    s [m $ dispose e, " represents the instruction to fetch ", m e, " to get its location ", m l, " and remove ", m l, " from the heap"]
    exneeded
  where
    e = "e"
    l = "l"


exampleProgram :: Note
exampleProgram = todo "A full example program"

separationLogicAxioms :: Note
separationLogicAxioms = do
    heapMutationAxiomSchemaDefinition
    disposalAxiomSchemaDefinition
    fetchAssignmentAxiomSchemaDefinition
    allocationAxiomSchemaDefinition
    frameRuleDefinition

heapMutationAxiomSchemaDefinition :: Note
heapMutationAxiomSchemaDefinition = de $ do
    s [m $ htrip (e .-> x) ((e .& hp) =:= f) (e .-> f), " is an ", axiomSchema, " in ", separationLogic]
  where
    e = "e"
    f = "f"
    x = "x"
    hp = "h"

disposalAxiomSchemaDefinition :: Note
disposalAxiomSchemaDefinition = de $ do
    s [m $ htrip (e .-> x) (dispose e) emp, " is an ", axiomSchema, " in ", separationLogic]
  where
    e = "e"
    x = "x"

fetchAssignmentAxiomSchemaDefinition :: Note
fetchAssignmentAxiomSchemaDefinition = de $ do
    s [m $ htrip (xx =: x ∧ e .-> yy) (x =:= (e .& hp)) (repl e xx x .-> yy ∧ yy =: x), " is an ", axiomSchema, " in ", separationLogic]
    newline
    s ["It means ", dquoted $ s ["If we know that a variable ", m x, " has location ", m xx, " and a expression ", m e, " points to a value ", m yy, " then, after we assign the location of ", m e, " to ", m x, ", we know that the expression ", m e, " with all ", m xx, "'s replaced by ", m x, " will now point to the value ", m yy, " and that ", m x, " now has location ", m yy]]
  where
    e = "e"
    x = "x"
    xx = "X"
    yy = "Y"
    hp = "h"

allocationAxiomSchemaDefinition :: Note
allocationAxiomSchemaDefinition = de $ do
    s [m $ htrip emp (x =:= cons [e0, dotsc, en]) (x ..-> [e0, dotsc, en]), " is an ", axiomSchema, " in ", separationLogic]
    s ["Note that ", m x, " must not appear in any of ", m $ cs [e0, dotsc, en]]
  where
    x = "x"
    e = "e"
    e0 = e !: 0
    en = e !: n
    n = "n"

frameRuleDefinition :: Note
frameRuleDefinition = de $ do
    lab frameRuleDefinitionLabel
    lab frameDefinitionLabel
    s ["The ", frameRule', " is the most important rule in ", separationLogic]
    prooftree $ framerule
        (assumption $ m $ htrip p cc q)
        (m $ htrip (p .* r) cc (q .* r))
    s ["Here, ", m r, " is called the ", frame']
    s ["Note that no variable modified by ", m cc, " may appear free in ", m r]
  where
    cc = "C"
    p = "P"
    q = "Q"
    r = "r"


tripleInterpretiation :: Note
tripleInterpretiation = de $ do
    s ["The interpretation of a triple in ", separationLogic, " needs to be extended from its interpretation in ", hoareLogic]
    s ["In ", separationLogic, " a triple ", m $ htrip p c q, " means ", dquoted $ s ["If ", m c, " is executed on a state satisfying ", m p, " then it will not fault, and if it terminates, that state will satisfy ", m q, " afterwards"]]
  where
    p = "P"
    c = "C"
    q = "Q"








