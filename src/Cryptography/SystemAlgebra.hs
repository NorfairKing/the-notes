module Cryptography.SystemAlgebra where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.BinaryOperation.Macro
import           Functions.BinaryOperation.Terms
import           Logic.FirstOrderLogic.Macro
import           Probability.ConditionalProbability.Macro
import           Probability.ConditionalProbability.Terms
import           Probability.Independence.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.RandomVariable.Terms
import           Relations.Domain.Terms
import           Sets.Basics.Terms

import           Cryptography.SymmetricCryptography.Macro

import           Cryptography.SystemAlgebra.Graph
import           Cryptography.SystemAlgebra.Macro
import           Cryptography.SystemAlgebra.Terms

systemAlgebraS :: Note
systemAlgebraS = section "System Algebra" $ do
    subsection "Abstract systems" $ do
        abstractSystemAlgebraDefinition
        abstractSystemAlgebraDefinitionNote
        systemAlgebraExamples

        subsubsection "Merging interfaces" $ do
            mergingInterfaces
            mergingInterfacesExamples

        subsubsection "2-systems" $ do
            twoSystemCompositionDefinition
            compositionOfTwoSystemsIsATwoSystem
            twoSystemCompositionAssociative

        subsubsection "Parallel composition" $ do
            parallelCompositionDefinition
            parallelCompositionExamples
            parallelCompositionOfTwoSystemsIsTwoSystem

        subsubsection "Resources and converters" $ do
            resourceDefinition
            converterDefinition
            converterExamples

    subsection "Discrete Single-Interface Systems" $ do
        subsubsection "(X,Y)-Systems" $ do
            xySystemsDefinition
            ySourceDefinition
            beaconDefinition
            bitStringBeaconDefinition
            uniformBitstringBeaconDefinition
            uniformRandomFunctionSystem
            xyOperationSystemDefinition
            synchronousParallelCompositionDefinition
            asynchronousParallelCompositionDefinition
        subsubsection "Environments" $ do
            environmentDefinition
            transcriptDefinition
        subsubsection "Probabillistic systems" $ do
            probabillisticSystemDefinition
            probabillisticEnvironmentDefinition
            probabillisticTranscriptDefinition
        subsubsection "Behaviours" $ do
            behaviourDefinition
            equivalentProbabillisticSystems
            behaviourOfEnvironmentDefinition
            probabillisticBeaconDefinition
            randomFunctionDefinition
            cumulativeDescriptionDefinition
            transcriptDistributionDefinition


abstractSystemAlgebraDefinition :: Note
abstractSystemAlgebraDefinition = de $ do
    lab abstractSystemAlgebraDefinitionLabel
    lab systemAlgebraDefinitionLabel
    lab systemDefinitionLabel
    lab labelDefinitionLabel
    lab interfaceLabelSetDefinitionLabel
    lab interfaceDefinitionLabel
    lab systemMergingOperationDefinitionLabel
    lab interfaceConnectionOperationDefinitionLabel
    s ["An", abstractSystemAlgebra', "consists of a", set, m syss_, "of", systems' <> ", a", set, m labs_, "of", labels' <> ", a", total, function, m $ fun laf_ syss_ (powset labs_), "that assigns the associated", interfaceLabelSet', "to each", system, "and two operations as follows"]
    itemize $ do
        item $ do
            s ["A", associative <> ",", commutative, systemMergingOperation', m $ fun2 smo_ syss_ syss_ syss_, "such that.."]
            let a = "A"
                b = "B"
            itemize $ do
                item $ s [m $ a `sm` b, "is only defined if", m $ la a ∩ la b, "is empty"]
                item $ m $ fa (a ∈ syss_) $ fa (b ∈ syss_) $ la (a `sm` b) =: la a ∪ la b
                item $ do
                    s ["Let", m emptysys, "be the", system, "such that", m $ la emptysys =: emptyset, "(if it exists)"]
                    ma $ fa (a ∈ syss_) $ a `sm` emptysys =: a =: emptysys `sm` a
                    todo "prove that this system is in fact unique"
        item $ do
            s ["An", associative, interfaceConnectionOperation', m $ fun3 (ico cdot_ cdot_ cdot_) syss_ labs_ labs_ syss_]
            let a = "A"
                l = "l"
                l1 = l !: 1
                l2 = l !: 2
            s ["Let", m a, "be a", system, "and let", m l1, and, m l2, "be two distinct", labels, "in", m $ la a]
            s [m $ ico a l1 l2, "is the", system, "that is identical to", m a, "except now the interfaces", m l1, and, m l2, "are connected"]
            ma $ la (ico a l1 l2) =: la a \\ setofs [l1, l2]
    s ["The above operations also have to be order invariant"]
    let a = "A"
        b = "B"
        l = "l"
        l1 = l !: 1
        l2 = l !: 2
    ma $ fa (cs [a, b] ∈ syss_) $ fa (cs [l1, l2] ∈ labs_) $ ico a l1 l2 `sm` b =: ico (pars $ a `sm` b) l1 l2

    let l = "L"
    s ["A system", m a, "with", m $ la a =: l, "is called an", m l <> "-" <> system', "or also a", m (setsize l) <> "-" <> system', "if the names of the labels aren't considered"]


abstractSystemAlgebraDefinitionNote :: Note
abstractSystemAlgebraDefinitionNote = nte $ do
    s ["We will generally only consider", abstractSystemAlgebras, "in which the", interfaceConnectionOperation, "is symmetric as follows"]
    let a = "A"
        l = "l"
        l1 = l !: 1
        l2 = l !: 2
    ma $ fa (a ∈ syss_) $ fa (cs [l1, l2] ∈ labs_) $ ico a l1 l2 =: ico a l2 l1



systemAlgebraExamples :: Note
systemAlgebraExamples = do
    let (a, b, c, d) = ("a", "b", "c", "d")
    ex $ do
        let sys = System "S" [a, b]
        systemFig 3 sys $ s ["An abstract", system, m "S", "with two interfaces:", m "a", and, m "b"]
    ex $ do
        let s1 = System "A" [a, b]
            s2 = System "B" [c, d]
            sys = Merge s1 s2
        systemFig 5 sys $ s ["The merger of two abstract", systems]

    ex $ do
        let s1 = System "S" [a, b, c]
            s2 = Connected a b s1
        systemsFig 3 [s1, s2] $ s ["The connection of the interfaces", m "a", and, m "b", "in the abstract", system, m "S"]

    ex $ do
        s ["Electronic components that can be connected to an electronic circuit forms a", systemAlgebra <> ", where the", systemMergingOperation, "means to place components on a board together and the", interfaceConnectionOperation, "means to place a wire between the interfaces"]



mergingInterfaces :: Note
mergingInterfaces = de $ do
    lab interfaceMergingDefinitionLabel
    s ["Given a", systemAlgebra, "we define a composite operation called", interfaceMerging', "as follows"]
    let a = "A"
        l = "L"
        j = "j"
    s ["Denote the interface merging operation on a", system, m a, "of an", interface, set, "with", labels, m l, "into an", interface, "with label", m j, "as" , m $ mio a l j]
    s ["The inverse operation is denoted as", m $ mioi a j l]
    s ["These operations have the following properties"]
    itemize $ do
        item $ m $ fa (a ∈ syss_) $ fa (l ⊆ la a) $ fa (j ∈ labs_ \\ la a) $ la (mio a l j) =: (pars $ la a \\ l) ∪ (setof j)
        item $ m $ fa (a ∈ syss_) $ fa (l ⊆ la a) $ fa (j ∈ labs_ \\ la a) $ la (mioi a j l) =: (pars $ la a \\ setof j) ∪ l
        item $ m $ mioi (pars $ mio a l j) j l =: a

mergingInterfacesExamples :: Note
mergingInterfacesExamples = do
    ex $ do
        let (a, b, c, d, e, l) = ("a", "b", "c", "d", "e", "l")
        let sys = System "A" [a, b, c, d, e]
        systemsFig 5 [sys, MergeLabels [a, b, c] l sys] $ do
            s ["The system on the right represents the merger of the interfaces", m "a" <> ", " <> m "b", and, m "c", "into", m "l", "from the system on the left"]

twoSystemCompositionDefinition :: Note
twoSystemCompositionDefinition = de $ do
    let s1 = "S" !: 1
        s2 = "S" !: 2
        l = "l"
        l1 = l !: 1
        l2 = l !: 2
    s [the, "(serial)", composition', "of two", m 2 <> "-" <> systems, "(with disjoint", interfaceLabelSets <> ")", "on two", labels, m l1, and, m l2, "where", m l1, "is in the", interfaceLabelSet, "of", m s1, and, m l2, "is in the", interfaceLabelSet, "of", m s2, "is defined as the merger of", m s1, and, m s2, "followed by the connection of", m l1, and, m l2, "in the result"]

compositionOfTwoSystemsIsATwoSystem :: Note
compositionOfTwoSystemsIsATwoSystem = do
    thm $ do
        s [the, composition, "of two", m 2 <> "-" <> systems, "is again a", m 2 <> "-" <> system]
        noproof
    ex $ do
        let (a, b, c, d) = ("a", "b", "c", "d")
        let s1 = System "A" [a, b]
            s2 = System "B" [c, d]
            sys = compose b c s1 s2
        systemFig 3 sys $ s ["The composition of two", m 2 <> "-" <> systems]

twoSystemCompositionAssociative :: Note
twoSystemCompositionAssociative = thm $ do
    s [the, composition, "of", m 2 <> "-" <> systems, "is", associative]
    toprove

parallelCompositionDefinition :: Note
parallelCompositionDefinition = de $ do
    lab parallelCompositionDefinitionLabel
    let s_ = "s"
        s1 = s_ !: 1
        s2 = s_ !: 2
        k = "k"
        sk = s_ !: k
        sl = list s1 s2 sk
    s ["Let", m sl, "be", systems, "in a", systemAlgebra, "with the same", interfaceLabelSet]
    let sn = sqbrac sl
    s ["Let", m sn, "be the", system <> ", obtained by relabeling the", interfaces, "of the", systems, m sl, "to be disjoint, then merging the", systems, "and then merging all parralel", interfaces, "into one interface with the same name"]
    s [m sn, "is called the", parallelComposition', "of", m sl]


parallelCompositionExamples :: Note
parallelCompositionExamples = do
    ex $ do
        let (a, b, c) = ("a", "b", "c")
        let s1 = System "A" [a, b, c]
            s2 = System "B" [a, b, c]
            sys = ParComp [s1, s2]
        systemFig 5 sys $ s ["The parallel composition of two abstract", systems]


parallelCompositionOfTwoSystemsIsTwoSystem :: Note
parallelCompositionOfTwoSystemsIsTwoSystem = do
    thm $ do
        s [the, parallelComposition, "of", m 2 <> "-" <> systems, "is a", m 2 <> "-" <> system]
        noproof
    ex $ do
        let (a, b) = ("a", "b")
        let s1 = System "A" [a, b]
            s2 = System "B" [a, b]
            s3 = System "C" [a, b]
            sys = ParComp [s1, s2, s3]
        systemFig 6 sys $ s ["The parallel composition of three 2-", systems]



resourceDefinition :: Note
resourceDefinition = de $ do
    lab resourceSystemDefinitionLabel
    lab resourceDefinitionLabel
    let i = mathcal "I"
    s ["An", m i <> "-" <> resourceSystem', "or simply", m i <> "-" <> resource, "is a", system, "with", interfaceLabelSet, m i]

converterDefinition :: Note
converterDefinition = de $ do
    lab converterSystemDefinitionLabel
    lab converterDefinitionLabel
    s ["A", converterSystem', "or simply", converter', "is a", system, "with two", interfaces <> ", an inside and an outside interface"]
    let a = alpha
        r = "R"
        i = mathcal "I"
    s [the, "inside", interface, "of a", converterSystem, m a, "can be connected to an", interface, "of an", m i <> "-" <> resourceSystem, m r <> ", resulting in a new", resourceSystem, "of the same type as", m r, "where the outside interface of", m a, "serves as the new interface of the combined system"]
    s ["If", m r, "is a", m 1 <> "-" <> system, "then the resulting", m 1 <> "-" <> system, "is denoted as", m $ conv_ a r]
    let i_ = "i"
    s ["Otherwise, if", m a, "is connected to interface", m $ i_ ∈ i, "of", m r, "the resulting", system, "is denoted as", m $ conv a i_ r]

converterExamples :: Note
converterExamples = do
    ex $ do
        let (a, b, c, d, e) = ("a", "b", "c", "in", "out")
        let r = System "R" [a, b, c]
            co = System "c" [d, e]
            sys = compose c d r co
        systemFig 6 sys $ s ["The conversion of a", resourceSystem, m "R", "with a converter", m "c"]

conversionOrderDoesNotMatter :: Note
conversionOrderDoesNotMatter = thm $ do
    s ["When two", converters, "are connected to distinct", interfaces, "of a", resource, "their order of conversion does not matter"]
    let a = alpha
        i = "i"
        b = beta
        j = "j"
        r = "R"
    ma $ conv a i (conv b j r) =: conv b j (conv a i r)
    noproof

xySystemsDefinition :: Note
xySystemsDefinition = de $ do
    let f = "f"
        x = mathcal "X"
        y = mathcal "Y"
        i = "i"
        f_ i = f !: i
        x_ i = "x" !: i
        y_ i = "y" !: i
    s ["A", system, "that computes a", function, m $ fun f x y, "for every new input, i.e.,", m (y_ i =: fn (f_ i) (x_ i)) <> ",is called an", m (tuple x y) <> "-" <> system']
    let r = "R"
    s ["More precicely, an", xyS x y, m r, "is a", nS 1, "that takes inputs from a", countable, set, m x, "and generates an output from a", countable, set, m y, "that possibly depends on an internal state of the", system]

    todo "define it more formaly with state space and transitions etc"


ySourceDefinition :: Note
ySourceDefinition = de $ do
    lab sourceDefinitionLabel
    let y = mathcal "Y"
    s ["An", m y <> "-" <> source', system, "is a", nS 1, "that only takes trigger inputs (with a unary alphabet) and (probabillistically) produces, for each trigger input, an output in", m y, "based on previous output"]


beaconDefinition :: Note
beaconDefinition = de $ do
    lab beaconDefinitionLabel
    s ["A memoryless", source <> ", outputting independent uniform", randomVariables, "is called a", beacon']


bitStringBeaconDefinition :: Note
bitStringBeaconDefinition = de $ do
    let n = "n"
    s ["A", beacon, "with domain", m $ bitss n, "is denoted as", m $ bitsbea n]

uniformBitstringBeaconDefinition :: Note
uniformBitstringBeaconDefinition = de $ do
    let n = "n"
    s ["A", beacon, "with domain", m $ bitss n, "that outputs a uniform random", m n <> "-bit string", "is denoted as", m $ ubitsbea n]

uniformRandomFunctionSystem :: Note
uniformRandomFunctionSystem = de $ do
    lab uniformRandomFunctionDefinitionLabel
    lab uRFDefinitionLabel
    let x = mathcal "X"
        y = mathcal "Y"
    s ["A", uniformRandomFunction', "(" <> uRF' <> ")", "from some", domain, m x, "to some", finite, range, m y, "is a memoryless", nS 1, "which, for every new input, replies with a uniformly random value, but replies consistently if a previously given input is repeated"]
    let m_ = "m"
        n_ = "n"
    s ["Typically we consider", m $ x =: bitss m_, and, m $ y =: bitss n_, "and denote such a", uRF, "as", m $ urf m_ n_]


xyOperationSystemDefinition :: Note
xyOperationSystemDefinition = de $ do
    let x = mathcal "X"
        y = mathcal "Y"
        a = "a"
        b = "b"
    s ["Consider two", xySs x y, m a, and, m b]
    s ["For a", binaryOperation, m binop_, "on", m y <> ", the", system, m $ a ★ b, "is the", xyS x y, "where the input is given to both", m a, and, m b, "and their outputs are combined using", m binop_, "as follows"]
    let f n = fn $ "f" .^: n .!: "i"
    let e = "x"
        x1 = e !: 1
        x2 = e !: 2
        i = "i"
        xi = e !: i
        lx = list x1 x2 xi
    ma $ f (a ★ b) lx =: f a lx ★ f b lx
    todo "what is this f doing here? is it a model of how the output can depend on the state? make that explicit!"

synchronousParallelCompositionDefinition :: Note
synchronousParallelCompositionDefinition = de $ do
    lab synchronousParallelCompositionDefinitionLabel
    let u = mathcal "U"
        v = mathcal "V"
        x = mathcal "X"
        y = mathcal "Y"
        a = "a"
        b = "b"
    s ["For an", xyS u v, m a, andan, xyS x y, m b <> ", the", synchronousParallelComposition, m $ syncomp a b, "is the", xyS (u ⨯ x) (v ⨯ y), "which takes pairs of inputs and returns the corresponding pairs of outputs as follows"]
    let f n = fn $ "f" .^: n .!: "i"
    let e = "x"
        x1 = e !: 1
        x2 = e !: 2
        i = "i"
        xi = e !: i
        d = "y"
        y1 = d !: 1
        y2 = d !: 2
        yi = d !: i
        lx = list x1 x2 xi
        ly = list y1 y2 yi
        lt = list (tuple x1 y1) (tuple x2 y2) (tuple xi yi)
    ma $ f (syncomp a b) lt =: f a lx ★ f b ly

asynchronousParallelCompositionDefinition :: Note
asynchronousParallelCompositionDefinition = de $ do
    lab asynchronousParallelCompositionDefinitionLabel
    let u = mathcal "U"
        v = mathcal "V"
        x = mathcal "X"
        y = mathcal "Y"
        a = "a"
        b = "b"
        uc = setcmpr (tuple 0 "u") ("u" ∈ u)
        xc = setcmpr (tuple 1 "x") ("x" ∈ x)
        vc = setcmpr (tuple 0 "v") ("v" ∈ v)
        yc = setcmpr (tuple 1 "y") ("y" ∈ y)
    s ["For an", xyS u v, m a, andan, xyS x y, m b <> ", the", synchronousParallelComposition, m $ asyncomp a b, "is the", ma (tuple (uc ∪ xc) (vc ∪ yc)) <> "-" <> system, "where each subsystem can be queried independently as follows"]
    let f n = fn $ "f" .^: n .!: "i"
    let e = "x"
        x1 = e !: 1
        x2 = e !: 2
        i = "i"
        xi = e !: i
        d = "y"
        y1 = d !: 1
        y2 = d !: 2
        yi = d !: i
        lx = list x1 x2 xi
        ly = list y1 y2 yi
        l0 = tuple 0 $ pars lx
        l1 = tuple 1 $ pars ly
    ma $ centeredBelowEachOther
        [ f (asyncomp a b) l0 =: f a lx
        , f (asyncomp a b) l1 =: f b ly
        ]

environmentDefinition :: Note
environmentDefinition = de $ do
    lab deterministicEnvironmentDefinitionLabel
    lab environmentDefinitionLabel
    let x = mathcal "X"
        y = mathcal "Y"
        g = "g"
        i = "i"
    s ["A", deterministicEnvironment, "for an", xyS x y, "(" <> "a " <> yxDE y x <> ")", "is a", constant, m $ g !: 0, "together with a", sequence, "of", functions, m $ sequ g i, "where", m $ fun g (y ^ (i - 1)) x]

transcriptDefinition :: Note
transcriptDefinition = de $ do
    lab transcriptDefinitionLabel
    let x = mathcal "X"
        y = mathcal "Y"
        i = "i"
        g = "g"
        a = "a"
        e = "e"
    s ["If an", xyS x y, m a, "is connected to a", yxDE y x, m e, "then an alternating", sequence, "of", elements, "in", m x, and, m y, "is generated as follows"]
    let x_ = ("x" !:)
        y_ = ("y" !:)
        g_ n = fn $ "g" .^: e .!: n
        f_ n = fn $ "f" .^: a .!: n
    ma $ leftBelowEachOther
        [ x_ 1 =: g !: 0
        , y_ 1 =: f_ 1 (cs [x_ 1])
        , x_ 2 =: g_ 1 (cs [y_ 1])
        , y_ 2 =: f_ 2 (cs [x_ 1, x_ 2])
        , x_ 3 =: g_ 2 (cs [y_ 1, y_ 2])
        , y_ 3 =: f_ 3 (cs [x_ 1, x_ 2, x_ 3])
        , x_ i =: g_ i (cs [y_ 1, y_ 2, dotsc, y_ (i - 1)])
        , y_ i =: f_ i (cs [x_ 1, x_ 2, dotsc, x_ i])
        ]
    s ["This alternating", sequence, "is called a", transcript', "and is denoted by", m $ transcr a e]

probabillisticSystemDefinition :: Note
probabillisticSystemDefinition = de $ do
    lab probabillisticSystemDefinitionLabel
    let x = mathcal "X"
        y = mathcal "Y"
    s ["A", probabillisticSystem', "(an " <> xyPS x y <> ")", "is a", randomVariable, "over the", set, "of", xyDSs x y]

probabillisticEnvironmentDefinition :: Note
probabillisticEnvironmentDefinition = de $ do
    lab probabillisticEnvironmentDefinitionLabel
    let x = mathcal "X"
        y = mathcal "Y"
    s ["A", probabillisticEnvironment', "(an " <> yxPE x y <> ")", "is a", randomVariable, "over the", set, "of", yxDEs x y]

probabillisticTranscriptDefinition :: Note
probabillisticTranscriptDefinition = de $ do
    lab probabillisticEnvironmentDefinitionLabel
    let x = mathcal "X"
        y = mathcal "Y"
        a = "A"
        e = "E"
    s ["Let", m a, "be an", xyPS x y, and, m e, "a", yxPE x y]
    s [the, probabillisticTranscript, m $ transcr a e, "of", m a, and, m e, "is the", sequence, "of", randomVariables, "as defined for the deterministic case in", rawRef transcriptDefinitionLabel]


behaviourDefinition :: Note
behaviourDefinition = de $ do
    lab behaviourDefinitionLabel
    let xx = mathcal "X"
        yy = mathcal "Y"
        x = "X"
        y = "Y"
        a = "S"
        i = "i"
        p = "p" .^: a
        pi = p .!: (y !: i <> mid <> x ^ i <> ", " <> y ^ (i - 1))
        (.|.) a b = a <> mid <> b
    s [the, behaviour', m $ bhv x, "of a", xyPS xx yy, m a, "is the", sequence, "of", conditionalProbability, distributions, m $ sequ pi i, "as follows"]
    let x_ i = "x" !: i
        y_ i = "y" !: i
        f i n = fn ("f" .^: a .!: i) (cs n)
    ma $ belowEachOther [LeftColumn, LeftColumn]
        [ fn2 (p .!: ((y !: 1) .|. (x !: 1)))
              (y_ 1)
              (x_ 1)
          & "" =: prob (f 1 [x_ 1] =: y_ 1)
        , fn3 (p .!: ((y !: 2) .|. cs [tuple (x !: 1) (x !: 2), y !: 1]))
              (y_ 2)
              (tuple (x_ 1) (x_ 2))
              (y_ 1)
          & "" =: cprob (f 2 [x_ 1, x_ 2] =: y_ 2)
                  (f 1 [x_ 1] =: y_ 1)
        , fn3 (p .!: ((y !: 3) .|. cs [triple (x !: 1) (x !: 2) (x !: 3), tuple (y !: 1) (y !: 2)]))
              (y_ 3)
              (triple (x_ 1) (x_ 2) (x_ 3))
              (tuple (y_ 1) (y_ 2))
          & "" =: cprob (f 3 [x_ 1, x_ 2, x_ 3] =: y_ 3)
                  (cs [f 1 [x_ 1] =: y_ 1, f 2 [x_ 1, x_ 2] =: y_ 2])
        , "" & vdots
        , fn3 (p .!: ((y !: i) .|. cs [x ^: i, y ^: i - 1]))
              (y_ i)
              ("x" ^ i)
              ("y" ^ (i - 1))
          & "" =: cprob (f i ["x" ^ i] =: y_ i)
                  (cs [f 1 [x_ 1] =: y_ 1, f 2 [x_ 1, x_ 2] =: y_ 2, dotsc, f (i - 1) ["x" ^: (i - 1)] =: y_ (i - 1)   ])
        , "" & vdots
        ]
    s ["Note that we use", m $ "x" ^ i, "as an abbreviaton for", m $ cs [x_ 1, x_ 2, dotsc, x_ i] <> ",", m $ "y" ^ i, "for", m $ cs [y_ 1, y_ 2, dotsc, y_ i] ,"as well as", m $ x ^ i, "for", m $ cs [x !: 1, x !: 2, dotsc, x !: i]]



equivalentProbabillisticSystems :: Note
equivalentProbabillisticSystems = de $ do
    let x = mathcal "X"
        y = mathcal "Y"
    s ["Two", xyPSs x y, "are", defineTerm "equivalent", "if they have the same behaviour"]



behaviourOfEnvironmentDefinition :: Note
behaviourOfEnvironmentDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
        x = "X"
        y = "Y"
        e = "E"
        i = "i"
        p = "p" .^: e
        pi = p .!: (x !: i <> mid <> y ^ (i - 1) <> ", " <> x ^ (i - 1))
    s [the, behaviour', m $ bhv x, "of a", yxPE yy xx, m e, "is the", sequence, "of", conditionalProbability, distributions, m $ sequ pi i, "as follows"]
    todo "Define fully"

probabillisticBeaconDefinition :: Note
probabillisticBeaconDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
        xs = "X"
        ys = "Y"
        x = "x"
        y = "y"
        i = "i"
        p = "p"
        b = "B"
    s ["A", yB yy, "is a", system, m b, "with arbitrary input alphabet", m xx <> ",", "wich outputs a new", independent, "and uniformly distributed (over", m yy <> ") output", m $ ys !: i, "for every new input", m $ xs !: i]
    ma $ fn3 (p .^: b .!: (ys !: i <> mid <> cs [xs ^: i, ys ^: (i - 1)])) (y !: i) (x ^: i) (y ^: (i - 1)) =: (1 /: setsize yy)


randomFunctionDefinition :: Note
randomFunctionDefinition = de $ do
    s ["A", randomFunction', "for a finite input alphabet, is a", system, "which corresponds to a function table chosen according to some distribution"]
    s ["A", uniformRandomFunction', "is denoted as", uRF']
    s ["A", randomPermutation', "is a", system, "which corresponds to a function table chosen according to some distribution from the", set, "of", permutations]
    s ["A", uniformRandomPermutation', "is denoted as", uRP']
    todo "make this rigorous"

    todo "what's the problem with an infinite alphabet? p 62"
    todo "replace the previous definition"
    exneeded


cumulativeDescriptionDefinition :: Note
cumulativeDescriptionDefinition = de $ do
    lab cumulativeDescriptionDefinitionLabel
    let xx = mathcal "X"
        yy = mathcal "Y"
        xs = "X"
        ys = "Y"
        x = "x"
        y = "y"
        i = "i"
        a = "S"
        p = "p" .^: a
        cd_ i = p .!: ((ys ^ i) <> mid <> (xs ^ i))
        cd i = fn2 (cd_ i) (y ^ i) (x ^ i)
        od_ i = p .!: ((ys !: i) <> mid <> cs [xs ^: i, ys ^: (i - 1)])
        od i = fn3 (od_ i)
                   (y !: i)
                   (x ^: i)
                   (y ^: (i - 1))
    s ["An", xyPS xx yy, m a, "can be analyzed for a fixed list of inputs", m $ list (x !: 1) (x !: 2) (x !: i)]
    s [the, "list", m $ list (ys !: 1) (ys !: 2) (ys !: i), "is then a", randomVariable, "in itself and", m a, "defines its", conditionalProbability, distribution, m $ cd i]
    let j = "j"
    ma $ cd i
      =: prodcmpr (j =: 1) i (od j)
    s ["This", conditionalProbability, distribution, m $ cd_ i, "satisfies a consistency condition which captures that", m $ ys !: j, "will never depend on", m $ ys !: i, "for any", m i, "greater than", m j]
    s ["The original distributions", m $ od_ i, "can be computed from the distributions", m $ cd_ i, "according to the following equation"]
    ma $ od i =: ((cd i) /: (cd (i - 1)))
    toprove
    s ["Hence the", behaviour, "can be equivalently be defined as the", sequence, m $ sequ (cd_ i) i, "of", conditionalProbability, distributions]
    s [m $ cd_ i, "is called the", cumulativeDescription', "of", m a]


transcriptDistributionDefinition :: Note
transcriptDistributionDefinition = de $ do
    let xx = mathcal "X"
        yy = mathcal "Y"
        xs = "X"
        ys = "Y"
        x = "x"
        y = "y"
        i = "i"
        a = "A"
        e = "E"
    s ["As noted earlier, an", xyPS xx yy, m a, anda, yxPE yy xx, m e, "together define a random experiment where", m a, and, m e , "are independent, in which the transcript", m $ cs [xs !: 1, ys !: 1, xs !: 2, ys !: 3, dotsc, xs !: i, ys !: i, dotsc], "is defined"]
    let k = "k"
        seg k = xs ^ k <> ys ^ k
    s ["We denote the", randomVariable, "corresponding to the initial segment of the", transcript, "(up to the", m k <> "-th step) by", m $ seg k]
    s ["Its", probabilityDistribution, "can then be described in terms of the", behaviour, "of", m a, and, m e, "as follows"]
    let pr_ = pr $ seg k
        pr = ("Pr" .^: (a <> e) .!:)
        p = "p"
        pe_ = p .^: e
        pe = pe_ .!: (xs ^: i <> mid <> cs [xs ^: (i - 1), ys ^: (i - 1)])
        pec = pe_ .!: (xs ^: i <> mid <> ys ^: (i - 1))
        pa_ = p .^: a
        pa = pa_ .!: (ys ^: i <> mid <> cs [xs ^: i, ys ^: (i - 1)])
        pac = pa_ .!: (ys ^: i <> mid <> xs ^: (i - 1))
    aligneqs
        (fn2 pr_ (x ^ k) (y ^ k))
        [ prodcmpr (i =: 1) k $ fn3 pe (x !: i) (x ^: (i - 1)) (y ^ (i - 1))
                         `cdot` fn3 pa (y !: i) (x ^: i      ) (y ^ (i - 1))
        ,      fn2 pec (x ^: i) (y ^: (i - 1))
        `cdot` fn2 pac (y ^: i) (x ^: i)
        ]
    s ["Note that", m pr_, "only depends on the", behaviours, "of", m a, and, m e]
    s ["In such a random experiment, the", conditionalProbability, distribution, "of", m $ ys !: i, "given", m $ list (xs !: 1) (xs !: 2) (xs !: i), and, m $ list (ys !: 1) (ys !: 2) (ys !: i), "is equal to", m pa]
    ma $ pr (ys ^: i <> mid <> cs [xs ^: i, ys ^: (i - 1)]) =: pa
    s ["However, the analogous statement about the cumulative description does not hold for a general", environment]
    ma $ pr (ys ^: i <> mid <> xs ^: i) `neq` (pa_ .!: (ys ^: i <> mid <> xs ^: i))












