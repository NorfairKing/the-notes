module Logic.SeparationLogic where

import           Notes

import           Prelude                        (Either (..))

import           Functions.Application.Macro
import           Logic.AbstractLogic.Terms
import           Logic.FirstOrderLogic.Macro
import           Logic.HoareLogic.Macro         hiding (satis)
import           Logic.HoareLogic.Terms         hiding (satisfies, satisfies')
import           Logic.PropositionalLogic.Macro

import           Logic.SeparationLogic.Graph
import           Logic.SeparationLogic.Macro
import           Logic.SeparationLogic.Terms

separationLogicS :: Note
separationLogicS = section "Separation Logic" $ do
    subsection "Predicates" $ do

        heapDefinition

        separationLogicDefinition

        satisfiesDefinition

        emptyHeapSemanticsDefinition
        emptyHeapExample

        pointsToSemanticsDefinition
        pointsToExample

        separatingConjunctionSemanticsDefinition
        separatingConjunctionExample
        separatingConjunctionTheorems

        chainedPointsToDefinition
        chainedPointsToExample

        separatingImplicationSemanticsDefinition
        separatingImplicationExample

        satisfactionExamples

    subsection "Heap operations" $ do
        fetchAssignmentDefinition
        fetchAssignmentExamples

        heapMutationDefinition
        heapMutationExample

        allocationAssignmentDefinition
        allocationAssignmentExample

        disposalDefinition
        disposalExample

        exampleProgram


        separationLogicAxioms

        tripleInterpretiation
        programProofExample


heapDefinition :: Note
heapDefinition = do
    de $ do
        lab heapDefinitionLabel
        s ["A ", heap', " is a partial function from a set of locations (pointers) to values"]
        s ["The difference between a ", heap, " and a program state is that values on the heap can represent other locations on the heap"]
        s ["In this new model, variables will evaluate to locations"]
        s [the, heap, " will then tell us what the value is that is stored at that location"]
    nte $ do
        s ["Watch out, this means that variables aren't stored like they were before, now only references to variables are kept in the store"]


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
emptyHeapExample = ex $ do
    storeHeapFig
        ["e", "f"]
        []
        [] $
        s $ ["A situation in which ", m emp, " holds"]

pointsToSemanticsDefinition :: Note
pointsToSemanticsDefinition = do
    de $ do
        lab pointsToDefinitionLabel
        m $ ss (e .-> f) ⇔ setof ((e .: st) .-> (f .: st)) ∈ hp
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

separatingConjunctionTheorems :: Note
separatingConjunctionTheorems = do
    emptyHeapSeparatingConjunction

emptyHeapSeparatingConjunction :: Note
emptyHeapSeparatingConjunction = thm $ do
    lab emptyHeapSeparatingConjunctionTheoremLabel
    s ["The empty heap can be separatingly conjuncted with any assertion"]
    ma $ p ⇒ p .* emp
    toprove
  where
    p = "P"

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
    noindent
    storeHeapsFig
        [
          storeHeap
            ["x"]
            [("x", ["5"])]
            [(Left "x", ("x", 0))]
        , storeHeap
            ["y"]
            [("y", ["6"])]
            [(Left "y", ("y", 0))]
        , storeHeap
            ["x", "y"]
            [("x", ["5"]), ("y", ["6"])]
            [(Left "x", ("x", 0)), (Left "y", ("y", 0))]
        ]
        mempty
    s ["The first situation is an example of a situation in which ", m $ satis st hp ((pars $ x .-> 5) -* (pars $ x .-> 5 .* y .-> 6)), " holds."]
    s ["This assertion holds because the heap could be extended with the disjunct heap from the second situation to produce a heap (the one on the right), that satisfies ", m $ (x .-> 5 .* y .-> 6)]
  where
    hp = "h"
    st = "s"
    x = "x"
    y = "y"

satisfactionExamples :: Note
satisfactionExamples = do
    ex $ do
        noindent
        storeHeapsFig
            [
              storeHeap
                    ["x", "y"]
                    [("x", ["6", "7"]), ("y", ["6", "7"])]
                    [(Left "x", ("x", 0)), (Left "y", ("y", 0))]
            ,  storeHeap
                    ["x", "y"]
                    [("x", ["6", "7"])]
                    [(Left "x", ("x", 0)), (Left "y", ("x", 0))]
            ] $
            s ["Two situations ", m aa, " on the left and ", m bb, " on the right"]

        hereFigure $ do
            linedTable ["", aa, bb]
                [
                  [x ..-> [6,7]                                                     , f, t]
                , [x ..-> [6,7] .* t                                                , t, t]
                , [x ..-> [6,7] .* y ..-> [6,7]                                     , t, t]
                , [x ..-> [6,7] ∧  y ..-> [6,7]                                     , f, t]
                , [(pars $ x ..-> [6,7] .* true) ∧ (pars $ y ..-> [6,7] .* true)    , t, t]
                ]
            caption $ "Assertions on the situations"
        s ["The first assertion doesn't hold for situation ", m aa, " because there are more elements on the heap than just the two mentioned in ", m $ x ..-> [4,4]]
        s ["The third assertion doesn't hold for situation ", m bb, " because the heap cannot be divided into two parts"]
        s ["The fourth assertion doesn't hold for situation ", m aa, " because there are too many elements on the heap"]
    ex $ do
        examq eth "Software Verification" "December 2014"
        storeHeapFig
            ["x", "y"]
            [("x", ["6", "7"]), ("y", ["8"])]
            [(Left "x", ("x", 0)), (Left "y", ("y", 0))] $
            s ["A situation in which ", m $ x ..-> [6, 7] .* (not . pars $ x ..-> [6, 7]), " holds"]
        storeHeapFig
            ["x", "y"]
            [("x", ["6", "7"])]
            [(Left "x", ("x", 0)), (Left "y", ("x", 0))] $
            s ["A situation in which ", m $ x ..-> [6, 7] ∧ (y ..-> [6, 7]), " holds"]
        storeHeapsFig
            [
              storeHeap
                ["z"]
                [("z", ["6", "7"])]
                [(Left "z", ("z", 0))]
            , storeHeap
                ["x", "y"]
                []
                []
            ] $
            s ["Two situations in which ", m $ emp ⇒ x =: y, " holds"]
        storeHeapFig
            ["x"]
            [("i", [" "]), ("j", [" "])]
            [(Left "x", ("i", 0)), (Right ("i", 0), ("j", 0)), (Right ("j", 0), ("j", 0))] $
            s ["A situation in which ", m $ te i $ x .-> i .* i .-> i, " holds"]
    ex $ do
        examq eth "Software Verification" "December 2013"
        s ["A well-formed binary tree ", m "t", " is defined by the following grammar"]
        ma $ "t" === n <> mid <> tuple t1 t2
        s ["These symbols have the following semantics"]
        itemize $ do
            item $ m $ (tree n i) ⇔ (i .-> n)
            item $ m $ (tree (tuple t1 t2) i) ⇔ (te (cs [l, r]) $ i ..-> [l, r] .* tree t1 l .* tree t2 r)
        storeHeapFig
            ["x"]
            [("x", [" ", " "]), ("y", ["7"]), ("z", ["8"])]
            [(Left "x", ("x", 0)), (Right ("x", 0), ("y", 1)), (Right ("x", 1), ("z", 1))] $
            s ["An example of a situation in which ", m $ tree (tuple 7 8) x, " holds"]
        storeHeapFig
            ["x", "y"]
            [("x", ["5"])]
            [(Left "x", ("x", 0)), (Left "y", ("x", 0))] $
            s ["An example of a situation in which ", m $ (tree 5 x) ∧ (tree 5 y), " holds"]
        storeHeapFig
            ["x"]
            [("x", [" ", " "]), ("y", [" ", " "]), ("a", ["1"]), ("b", ["2"]), ("c", ["3"])]
            [(Left "x", ("x", 0)), (Right ("x", 0), ("y", 0)), (Right ("x", 1), ("a", 0)), (Right ("y", 1), ("b", 0)), (Right ("y", 0), ("c", 0))] $
            s ["An example of a situation in which ", m $ tree (tuple (tuple 3 2) 1) x, " holds"]

  where
    tree = fn2 "tree"
    t = true
    f = false
    t1 = "t" !: 1
    t2 = "t" !: 2
    aa = "A"
    bb = "B"
    i = "i"
    l = "l"
    n = "n"
    r = "r"
    x = "x"
    y = "y"

fetchAssignmentDefinition :: Note
fetchAssignmentDefinition = de $ do
    s [m $ e .& hp, " represents the location of the variable that is said to be stored in ", m e]
  where
    hp = "h"
    e = "e"

fetchAssignmentExamples :: Note
fetchAssignmentExamples = do
    ex $ do
        noindent
        storeHeapsFig
            [
              storeHeap
                    ["x", "y"]
                    [("x", ["4"]), ("y", ["3"])]
                    [(Left "x", ("x", 0)), (Left "y", ("y", 0))]
            , storeHeap
                    ["x", "y"]
                    [("x", ["4"]), ("y", ["3"])]
                    [(Left "x", ("y", 0)), (Left "y", ("y", 0))]
            ] $
            s ["An example situation before and after a ", m $ x =:= (y .& hp), " assignment"]
        s ["Note that this example is slightly misleading because the variable stored in y is a value and not a pointer"]
        s ["The next example should clear up the confusion"]
    ex $ do
        storeHeapsFig
            [
              storeHeap
                    ["x", "y"]
                    [("x", ["4"]), ("y", [" "]), ("z", ["5"])]
                    [(Left "x", ("x", 0)), (Left "y", ("y", 0)), (Right ("y", 0), ("z", 0))]
            , storeHeap
                    ["x", "y"]
                    [("x", ["4"]), ("y", [" "]), ("z", ["5"])]
                    [(Left "x", ("z", 0)), (Left "y", ("y", 0)), (Right ("y", 0), ("z", 0))]
            ] $
            s ["An example situation before and after a ", m $ x =:= (y .& hp), " assignment"]
  where
    x = "x"
    y = "y"
    hp = "h"


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
    storeHeapsFig
        [
          storeHeap
                ["x", "y"]
                [("x", ["2","4"]), ("y", ["3","5"])]
                [(Left "x", ("x", 0)), (Left "y", ("y", 0))]
        , storeHeap
                ["x", "y"]
                [("x", ["2"," "]), ("y", ["3","5"])]
                [(Left "x", ("x", 0)), (Left "y", ("y", 0)), (Right ("x", 1), ("y", 0))]
        ] $
        s ["An example situation before and after a ", m $ ((x + 1) .& hp) =:= y, " instruction"]
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
    lab disposalDefinitionLabel
    s [m $ dispose e, " represents the instruction to fetch ", m e, " to get its location ", m l, " and remove ", m l, " from the heap"]
  where
    e = "e"
    l = "l"

disposalExample :: Note
disposalExample = ex $ do
    noindent
    storeHeapsFig
        [
          storeHeap
                ["x"]
                [("x", ["2","4", "8"])]
                [(Left "x", ("x", 0))]
        , storeHeap
                []
                [("x", [" ","4", "8"])]
                []
        ] $
        s ["An example situation before and after a ", m $ dispose "x", " instruction"]

exampleProgram :: Note
exampleProgram = ex $ do
    lab separationLogicProgramExampleLabel
    s ["In this example, we'll look at the following simple program and what it does to its store/heap situation"]
    ma $ seqins
        [
          x =:= cons [3, 3]
        , y =:= cons [4, 4]
        , ((x + 1) .& hp) =:= y
        , ((y + 1) .& hp) =:= x
        , y =:= x + 1
        , dispose x
        , y =:= (y .& hp)
        ]
    s ["Starting from an empty heap, after the first two instructions the situation will be as follows"]
    storeHeapFig
            ["x", "y"]
            [("x", ["3","3"]), ("y", ["4","4"])]
            [(Left "x", ("x", 0)), (Left "y", ("y", 0))]
            mempty

    s ["The following two instructions leave the situation as follows"]
    storeHeapFig
            ["x", "y"]
            [("x", ["3"," "]), ("y", ["4"," "])]
            [(Left "x", ("x", 0)), (Left "y", ("y", 0)), (Right ("x", 1), ("y", 0)), (Right ("y", 1), ("x", 0))]
            mempty
    s ["After the fifth instruction, the situation looks as follows"]
    storeHeapFig
            ["x", "y"]
            [("x", ["3"," "]), ("y", ["4"," "])]
            [(Left "x", ("x", 0)), (Left "y", ("x", 1)), (Right ("x", 1), ("y", 0)), (Right ("y", 1), ("x", 0))]
            mempty
    s ["The dispose instruction disposes of some allocated heap space but there still exist pointers to it"]
    storeHeapFig
            ["x", "y"]
            [("x", [" "," "]), ("y", ["4"," "])]
            [(Left "x", ("x", 0)), (Left "y", ("x", 1)), (Right ("x", 1), ("y", 0)), (Right ("y", 1), ("x", 0))]
            mempty
    s ["Lastly, the last instruction leaves the heap as follows"]
    storeHeapFig
            ["x", "y"]
            [("x", [" "," "]), ("y", ["4"," "])]
            [(Left "x", ("x", 0)), (Left "y", ("y", 0)), (Right ("x", 1), ("y", 0)), (Right ("y", 1), ("x", 0))]
            mempty


  where
    -- st = "s"
    hp = "h"
    x = "x"
    y = "y"

separationLogicAxioms :: Note
separationLogicAxioms = subsection "Axioms and inference rules" $ do
    heapMutationAxiomSchemaDefinition
    disposalAxiomSchemaDefinition
    fetchAssignmentAxiomSchemaDefinition
    allocationAxiomSchemaDefinition
    frameRuleDefinition

heapMutationAxiomSchemaDefinition :: Note
heapMutationAxiomSchemaDefinition = de $ do
    lab heapMutationDefinitionLabel
    s [m $ htrip (e .-> x) ((e .& hp) =:= f) (e .-> f), " is an ", axiomSchema, " in ", separationLogic]
    s ["This is called the ", heapMutation', " ", axiomSchema]
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
    lab allocationDefinitionLabel
    s [m $ htrip emp (x =:= cons [e0, dotsc, en]) (x ..-> [e0, dotsc, en]), " is an ", axiomSchema, " in ", separationLogic]
    s ["Note that ", m x, " must not appear in any of ", m $ cs [e0, dotsc, en]]
    s ["This is called the ", allocation', " ", axiomSchema]
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


programProofExample :: Note
programProofExample = ex $ do
    s ["Retaking the program from an earlier example", ref separationLogicProgramExampleLabel, ", we will now prove the following triple"]
    ma $ htrip p_ prog q_
    s ["In ", separationLogic, " proofs we reason forwards rather than backwards like in ", hoareLogic]
    s ["We start with an empty heap and see the first instruction: ", m prog1]
    s ["Applying the ", allocation, " ", axiomSchema, " gets us the following triple"]
    let prog1q_ = (x ..-> [3, 3])
    ma $ htrip p_ prog1 prog1q_
    s ["We get something similar by applying the same axiom schema to the second instruction"]
    let prog2q_ = (y ..-> [4, 4])
    ma $ htrip p_ prog2 prog2q_
    s ["But now these need to be combined before we can go on"]
    s ["Note first that we can separatingly conjoin an empty heap to the postcondition of the first triple as follows", ref emptyHeapSeparatingConjunctionTheoremLabel]
    let prog1q_' = (x ..-> [3, 3] .* emp)
    ma $ prog1q_ ⇒ prog1q_'
    s ["We can then apply the rule of ", consequence_]
    prooftree $ conseq2
                    (assumption $ m $ htrip p_ prog1 prog1q_)
                    (assumption $ m $ prog1q_ ⇒ prog1q_')
                    (m $ htrip p_ prog1 prog1q_')
    let f1_ = x ..-> [3, 3]
    s ["Now we can use the ", frameRule, " to the second triple we found with ", m f1_, " as a frame"]
    let prog2q_' = (prog2q_ .* f1_)
    prooftree $ framerule
                    (assumption $ m $ htrip p_ prog2 prog2q_)
                    (m $ htrip prog1q_' prog2 prog2q_')
    s ["Finally we can use the rule of ", sequentialComposition_, " to combine the first two instructions"]
    prooftree $ seqcomp
                    (assumption $ m $ htrip p_ prog1 prog1q_')
                    (assumption $ m $ htrip prog1q_' prog2 prog2q_')
                    (m $ htrip p_ (seqins [prog1, prog2]) prog2q_')
    s ["The next two instructions give us similar triples using the ", heapMutation, " ", axiomSchema]
    let prog3p_ = x + 1 .-> 3
        prog3q_ = x + 1 .-> y
    ma $ htrip prog3p_ prog3 prog3q_
    let prog4p_ = y + 1 .-> 4
        prog4q_ = y + 1 .-> x
    ma $ htrip prog4p_ prog4 prog4q_

    let f2_ = y ..-> [4, 4] .* x .-> 3
    s ["We can apply the frame rule with frame ", m f2_]
    let prog3p_' = f2_ .* prog3p_
    let prog3q_' = f2_ .* prog3q_
    prooftree $ framerule
                    (assumption $ m $ htrip prog3p_ prog3 prog3q_)
                    (m $ htrip prog3p_' prog3 prog3q_')
    s ["Now we can add the third instruction to the list using the ", sequentialComposition, " rule"]
    prooftree $ seqcomp
                    (assumption $ m $ htrip_ p_ (seqins [prog1, prog2]) prog2q_')
                    (assumption $ m $ htrip_ prog3p_' prog3 prog3q_')
                    (m $ htrip p_ (seqins [prog1, prog2, prog3]) prog3q_')

    let f3_ = x ..-> [3, y] .* y .-> 4
    s ["Analogously we can use the frame rule with frame ", m f3_, " and another application of sequential composition to move forward another instruction"]
    let prog4p_' = f3_ .* prog4p_
    let prog4q_' = f3_ .* prog4q_
    prooftree $ framerule
                    (assumption $ m $ htrip prog4p_ prog4 prog4q_)
                    (m $ htrip prog4p_' prog4 prog4q_')
    prooftree $ seqcomp
                    (assumption $ m $ htrip_ p_ (seqins [prog1, prog2, prog3]) prog3q_')
                    (assumption $ m $ htrip_ prog4p_' prog4 prog4q_')
                    (m $ htrip p_ (seqins [prog1, prog2, prog3, prog4]) prog4q_')

    s ["The forward assignment axiom schema", ref forwardAssignmentDefinitionLabel, " gives us a triple concerning the fifth instruction"]
    let f4_ = x ..-> [3, y] .* y ..-> [4, x]
    let f4_' = x ..-> [3, yo] .* yo ..-> [4, x]
    let prog5q_ = (pars f4_') ∧ (pars $ y =: x + 1)
    ma $ htrip
        f4_
        (y =:= x + 1)
        prog5q_

    s ["Another application of the rule of ", sequentialComposition, " adds the fifth instruction to the list"]
    prooftree $ seqcomp
                    (assumption $ m $ htrip_ p_ (seqins [prog1, prog2, prog3, prog4]) prog4q_')
                    (assumption $ m $ htrip_ f4_ prog5 prog5q_)
                    (m $ htrip_ p_ (seqins [prog1, prog2, prog3, prog4, prog5]) prog5q_)

    s ["We use the ", disposal, " ", axiomSchema, " to get a triple involving the sixth instruction"]
    let prog6p_ = (x .-> 3)
    let prog6q_ = emp
    ma $ htrip prog6p_ prog6 prog6q_

    let f5_ = x + 1.-> yo .* yo ..-> [4, x] ∧ (y =: x + 1)
    s ["We use the ", frameRule, " with frame ", m f5_, " as follows"]
    let prog6p_' = prog6p_ .* f5_
    let prog6q_' = prog6q_ .* f5_
    prooftree $ framerule
                    (assumption $ m $ htrip prog6p_ prog6 prog6q_)
                    (m $ htrip prog6p_' prog6 prog6q_')

    s ["The rule of consequence allows us to rewrite that postcondition because ", m (emp .* p), " implies ", m p, " for any ", m p]
    let prog6q_'' = f5_
    prooftree $ conseq2
                (assumption $ m $ htrip_ prog6p_' prog6 prog6q_')
                (assumption $ m $ centeredBelowEachOther [prog6p_', " " ⇒ " ", prog6q_''])
                (m $ htrip_ prog6p_' prog6 prog6q_'')

    s ["Once more, the rule of sequential composition allows us to add an instruction to our list"]
    prooftree $ seqcomp
                (assumption $ m $ htrip_ p_ (seqins [prog1, prog2, prog3, prog4, prog5]) prog5q_)
                (assumption $ m $ htrip_ prog6p_' prog6 prog6q_'')
                (m $ htrip_ p_ (seqins [prog1, prog2, prog3, prog4, prog5, prog6]) prog6q_'')

    let prog7p_ = ((x + 1 =: y) ∧ y .-> yo)
    let prog7q_ = ((x + 1 =: yno) ∧ yno .-> yo ∧ y =: (yno .& hp))
    s ["The forward assignment axiom gets us another triple, this time concerning the seventh instruction"]
    ma $ htrip_ prog7p_ prog7 prog7q_
    s ["The postcondition in this triple can be rewritten by implication"]
    let prog7q_' = ((x + 1 =: yno) ∧ yno .-> yo ∧ y =: yo)
    let prog7q_'' = ((x + 1).-> yo ∧ y =: yo)
    ma $ centeredBelowEachOther $
        [
          prog7q_
        , "" ⇒ ""
        , prog7q_'
        , "" ⇒ ""
        , prog7q_''
        ]
    s ["The rule of consequence then gets us the according triple"]
    prooftree $ conseq2
                    (assumption $ m $ htrip_ prog7p_ prog7 prog7q_)
                    (assumption $ m $ centeredBelowEachOther [prog7q_, "" ⇒ "", prog7q_''])
                    (m $ htrip_ prog7p_ prog7 prog7q_'')

    let f7_ = yo ..-> [4,x]
    let prog7p_' = f7_ .* prog7p_
    let prog7q_''' = f7_ .* prog7q_''
    s ["The frame rule now lets us add a frame: ", m f7_]
    prooftree $ framerule
                    (assumption $ m $ htrip_ prog7p_ prog7 prog7q_'')
                    (m $ htrip_ prog7p_' prog7 prog7q_''')

    s ["Finally we can use the rule of ", sequentialComposition, " to get a triple about concerning the entire program"]
    prooftree $ seqcomp
                    (assumption $ m $ htrip_ p_ (seqins [prog1, prog2, prog3, prog4, prog5, prog6]) prog6q_'')
                    (assumption $ m $ htrip_ prog7p_' prog7 prog7q_''')
                    (m $ htrip_ p_ prog prog7q_''')

    s ["One last application of the rule of ", consequence, " completes the proof"]
    prooftree $ conseq2
                    (assumption $ m $ htrip_ p_ prog prog7q_''')
                    (assumption $ m $ centeredBelowEachOther [prog7q_''', "" ⇒ "", q_])
                    (m $ htrip_ p_ prog q_)


  where
    prog = seqins
        [
          prog1
        , prog2
        , prog3
        , prog4
        , prog5
        , prog6
        , prog7
        ]
    prog1 = x =:= cons [3, 3]
    prog2 = y =:= cons [4, 4]
    prog3 = ((x + 1) .& hp) =:= y
    prog4 = ((y + 1) .& hp) =:= x
    prog5 = y =:= x + 1
    prog6 = dispose x
    prog7 = y =:= (y .& hp)
    p_ = emp
    q_ = (y .-> 4) .* true
    p = "P"

    hp = "h"
    x = "x"
    y = "y"
    yo = y ^: "old"
    yno = y ^: "newold"



















