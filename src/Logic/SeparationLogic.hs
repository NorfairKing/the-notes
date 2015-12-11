module Logic.SeparationLogic where

import           Notes

import           Prelude                     (Bool (..), Either (..))

import           Logic.AbstractLogic
import           Logic.HoareLogic.Macro      hiding (satis)
import           Logic.HoareLogic.Terms      hiding (satisfies, satisfies')
import           Logic.SeparationLogic.Graph
import           Logic.SeparationLogic.Macro
import           Logic.SeparationLogic.Terms

separationLogicS :: Notes
separationLogicS = notesPart "separation-logic" $ do
    section "Separation Logic"

    heapDefinition

    separationLogicDefinition

    satisfiesDefinition

    emptyHeapSemanticsDefinition
    emptyHeapExample

    pointsToSemanticsDefinition
    pointsToExample

    separatingConjunctionSemanticsDefinition
    separatingConjunctionExample

    chainedPointsToDefinition
    chainedPointsToExample

    separatingImplicationSemanticsDefinition
    separatingImplicationExample

    satisfactionExamples


    fetchAssignmentDefinition

    heapMutationDefinition
    heapMutationExample

    allocationAssignmentDefinition
    allocationAssignmentExample

    disposalDefinition
    disposalExample


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
  where
    ss = satis st hp
    st = "s"
    hp = "h"

emptyHeapExample :: Note
emptyHeapExample = ex $ storeHeapFig ["e", "f"] [] [] (s $ ["A situation in which ", m emp, " holds"])

pointsToSemanticsDefinition :: Note
pointsToSemanticsDefinition = do
    de $ do
        lab pointsToDefinitionLabel
        m $ ss (e .-> f) ⇔ hp =§= ((e .: st) .-> (f .: st)) ∈ hp
        s ["... or informally: ", dquoted $ s ["There exists a value ", m f, " on the heap that ", m e, " (which may also be a value on the heap) points to and no others"]]
  where
    ss = satis st hp
    st = "s"
    hp = "h"
    e = "e"
    f = "f"

pointsToExample :: Note
pointsToExample = ex $ storeHeapFig
    ["e"]
    [("a", ["8"])]
    [(Left "e", ("a", 0))] $
    s $ ["A situation in which ", m $ "e" .-> 8, " holds"]



separatingConjunctionSemanticsDefinition :: Note
separatingConjunctionSemanticsDefinition = de $ do
    m $ ss (p .* q) ⇔ (te (cs [h1, h2]) $ between (comm0 "bot") h1 h2 ∧ between (comm0 "circ") h1 h2 =: hp ∧ satis st h1 p ∧ satis st h2 q)
    s ["... or informally: ", dquoted $ s ["The heap can be divided into two parts ", m h1, and, m h2, ", one where ", m $ satis st h1 p, " holds and one where ", m $ satis st h2 q]]
  where
    ss = satis st hp
    st = "s"
    hp = "h"
    h1 = hp !: 1
    h2 = hp !: 2
    p = "P"
    q = "Q"

separatingConjunctionExample :: Note
separatingConjunctionExample = ex $ storeHeapFig
    ["x", "y", "z"]
    [("5", ["5"]), ("z", ["z"]), ("10", ["10"])]
    [(Left "x", ("5", 0)), (Left "z", ("10", 0)), (Right ("5", 0), ("z", 0)), (Right ("z", 0), ("10", 0))] $
    s ["A situation in which ", m $ ss ("x" .-> 5 .* 5 .-> "z" .* "z" .-> 10), " holds"]
  where
    ss = satis st hp
    st = "s"
    hp = "h"

chainedPointsToDefinition :: Note
chainedPointsToDefinition = de $ do
    s ["The notation ", m $ e ..-> [f0, f1, dotsc, fn], " is a shorthand for the following"]
    ma $ (e .-> f0) .* (e + 1 .-> f1) .* dotsc .* ((e + n) .-> fn)
  where
    e = "e"
    f = "f"
    n = "n"
    f0 = f !: 0
    f1 = f !: 1
    fn = f !: n

chainedPointsToExample :: Note
chainedPointsToExample = ex $ storeHeapFig
    ["e"]
    [("a", ["1", "5"])]
    [(Left "e", ("a", 0))] $
    s $ ["A situation in which ", m $ "e" ..-> [1, 5], " holds"]


separatingImplicationSemanticsDefinition :: Note
separatingImplicationSemanticsDefinition = de $ do
    s [m $ satis st hp (p -* q), " is said to hold if and only if ", dquoted $ s ["Extending ", m hp, " with a disjoint part ", m hp', " that satisfies ", m p, " results in a new heap satisfying ", m q]]
  where
    hp = "h"
    hp' = "h'"
    st = "s"
    p = "P"
    q = "Q"

separatingImplicationExample :: Note
separatingImplicationExample = ex $ do
    fpa <- storeHeap
        ["x"]
        [("x", ["5"])]
        [(Left "x", ("x", 0))]
    fpb <- storeHeap
        ["y"]
        [("y", ["6"])]
        [(Left "y", ("y", 0))]
    fpc <- storeHeap
        ["x", "y"]
        [("x", ["5"]), ("y", ["6"])]
        [(Left "x", ("x", 0)), (Left "y", ("y", 0))]
    hereFigure $ do
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.25" <> textwidth)] fpa
        hspace  $ Cm 1.0
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.25" <> textwidth)] fpb
        hspace  $ Cm 1.0
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.25" <> textwidth)] fpc
    s ["The first situation is an example of a situation in which ", m $ satis st hp ((pars $ x .-> 5) -* (pars $ x .-> 5 .* y .-> 6)), " holds."]
    s ["This assertion holds because the heap could be extended with the disjunct heap from the second situation to produce a heap (the one on the right), that satisfies ", m $ (x .-> 5 .* y .-> 6)]
  where
    hp = "h"
    st = "s"
    x = "x"
    y = "y"

satisfactionExamples :: Note
satisfactionExamples = ex $ do
    noindent
    fpa <- storeHeap
                ["x", "y"]
                [("x", ["4","4"]), ("y", ["4","4"])]
                [(Left "x", ("x", 0)), (Left "y", ("y", 0))]
    fpb <- storeHeap
                ["x", "y"]
                [("x", ["4","4"])]
                [(Left "x", ("x", 0)), (Left "y", ("x", 0))]
    hereFigure $ do
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.25" <> textwidth)] fpa
        hspace  $ Cm 1.0
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.25" <> textwidth)] fpb
        caption $ s ["Two situations ", m aa, " on the left and ", m bb, " on the right"]

    hereFigure $ do
        linedTable ["", aa, bb]
            [
              [x ..-> [4,4]                                                     , f, t]
            , [x ..-> [4,4] .* t                                                , t, t]
            , [x ..-> [4,4] .* y ..-> [4,4]                                     , t, t]
            , [x ..-> [4,4] ∧  y ..-> [4,4]                                     , f, t]
            , [(pars $ x ..-> [4,4] .* true) ∧ (pars $ y ..-> [4,4] .* true)    , t, t]
            ]
        caption $ "Assertions on the situations"
    s ["The first assertion doesn't hold for situation ", m aa, " because there are more elements on the heap than just the two mentioned in ", m $ x ..-> [4,4]]
    s ["The third assertion doesn't hold for situation ", m bb, " because the heap cannot be divided into two parts"]
    s ["The fourth assertion doesn't hold for situation ", m aa, " because there are too many elements on the heap"]
  where
    t = true
    f = false
    x = "x"
    y = "y"
    aa = "A"
    bb = "B"

fetchAssignmentDefinition :: Note
fetchAssignmentDefinition = de $ do
    s [m $ e .& hp, " represents the location of the variable that is said to be stored in ", m e]
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

heapMutationExample :: Note
heapMutationExample = ex $ do
    noindent
    fpa <- storeHeap
                ["x", "y"]
                [("x", ["2","4"]), ("y", ["3","5"])]
                [(Left "x", ("x", 0)), (Left "y", ("y", 0))]
    fpb <- storeHeap
                ["x", "y"]
                [("x", ["2"," "]), ("y", ["3","5"])]
                [(Left "x", ("x", 0)), (Left "y", ("y", 0)), (Right ("x", 1), ("y", 0))]
    hereFigure $ do
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.25" <> textwidth)] fpa
        hspace  $ Cm 1.0
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.25" <> textwidth)] fpb
        caption $ s ["An example situation before and after a ", m $ ((x + 1) .& hp) =:= y, " instruction"]
  where
    x = "x"
    y = "y"
    hp = "h"

allocationAssignmentDefinition :: Note
allocationAssignmentDefinition = de $ do
    s [m $ cons [e1, dotsc, en], " represents the instruction to allocate ", m n, " consecutive locations that are not in the heap yet, say ", m $ cs [l1, dotsc, ln], " and assign the values of ", m $ cs [e1, dotsc, en], " to the contents of ", m $ cs [l1, dotsc, ln], " respectively"]
  where
    e = "e"
    e1 = e !: 1
    en = e !: n
    l = "l"
    l1 = l !: 1
    ln = l !: n
    n = "n"

allocationAssignmentExample :: Note
allocationAssignmentExample = ex $ storeHeapFig
    ["x"]
    [("x",["1", "2", "5"])]
    [(Left "x", ("x", 0))] $
    s $ ["The result of ", m $ x =:= cons [1, 2, 5], " starting from an empty heap"]
  where
    x = "x"

disposalDefinition :: Note
disposalDefinition = de $ do
    s [m $ dispose e, " represents the instruction to fetch ", m e, " to get its location ", m l, " and remove ", m l, " from the heap"]
  where
    e = "e"
    l = "l"

disposalExample :: Note
disposalExample = ex $ do
    noindent
    fpa <- storeHeap
                ["x"]
                [("x", ["2","4", "8"])]
                [(Left "x", ("x", 0))]
    fpb <- storeHeap
                []
                [("x", [" ","4", "8"])]
                []
    hereFigure $ do
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.25" <> textwidth)] fpa
        hspace  $ Cm 1.0
        includegraphics [KeepAspectRatio True, IGHeight (Cm 3.0), IGWidth (CustomMeasure $ "0.25" <> textwidth)] fpb
        caption $ s ["An example situation before and after a ", m $ dispose "x", " instruction"]



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
    s [m $ htrip (te x $ e .-> x) ((e .& hp) =:= f) (e .-> f), " is an ", axiomSchema, " in ", separationLogic]
  where
    e = "e"
    f = "f"
    x = "x"
    hp = "h"

disposalAxiomSchemaDefinition :: Note
disposalAxiomSchemaDefinition = de $ do
    s [m $ htrip (te x $ e .-> x) (dispose e) emp, " is an ", axiomSchema, " in ", separationLogic]
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








