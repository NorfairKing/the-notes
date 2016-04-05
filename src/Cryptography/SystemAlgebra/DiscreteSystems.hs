module Cryptography.SystemAlgebra.DiscreteSystems where

import           Notes                                            hiding
                                                                   (cyclic)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.BinaryOperation.Macro
import           Functions.BinaryOperation.Terms
import           LinearAlgebra.VectorSpaces.Terms
import           Logic.FirstOrderLogic.Macro
import           Probability.ConditionalProbability.Macro
import           Probability.ConditionalProbability.Terms
import           Probability.Distributions.Terms
import           Probability.Independence.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.ProbabilityMeasure.Terms
import           Probability.RandomVariable.Terms
import           Relations.Domain.Terms
import           Sets.Basics.Terms

import           Cryptography.SymmetricCryptography.Macro

import           Cryptography.SystemAlgebra.AbstractSystems.Macro
import           Cryptography.SystemAlgebra.AbstractSystems.Terms
import           Cryptography.SystemAlgebra.DiscreteSystems.Macro
import           Cryptography.SystemAlgebra.DiscreteSystems.Terms

discreteSystemsSS :: Note
discreteSystemsSS = subsection "Discrete Single-Interface Systems" $ do
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
        restrictedSystemDefinition
    subsubsection "Environments" $ do
        environmentDefinition
        restrictedEnvironmentDefinition
        transcriptDefinition
    subsubsection "Probabillistic systems" $ do
        probabillisticSystemDefinition
        probabillisticEnvironmentDefinition
        probabillisticTranscriptDefinition
    subsubsection "Behaviours" $ do
        behaviourDefinition
        equivalentProbabillisticSystems
        behaviourExamples
        behaviourOfEnvironmentDefinition
        equivalentProbabillisticEnvironments
        probabillisticBeaconDefinition
        randomFunctionDefinition
        cumulativeDescriptionDefinition
        transcriptDistributionDefinition


xySystemsDefinition :: Note
xySystemsDefinition = de $ do
    let f = "f"
        x = mathcal "X"
        y = mathcal "Y"
        i = "i"
        f_ i = f !: i
        x_ i = "x" !: i
        y_ i = "y" !: i
    s ["A", system, "that computes a", function, m $ fun (f_ i) (x ^ i) y, "for every new input, i.e.,", m (y_ i =: fn (f_ i) (x_ i)) <> ", is called an", m (tuple x y) <> "-" <> system']
    let r = "R"
    s ["More precicely, an", xyS x y, m r, "is a", nS 1, "that takes inputs from a", countable, set, m x, "and generates an output from a", countable, set, m y, "that possibly depends on an internal state of the", system]
    s ["Formally, this is described as a", sequence, m $ sequ (f_ i) i, "of", functions, "as follows"]
    ma $ leftBelowEachOther $
        [ func (f_ 1) (x ^ 1) y (x_ 1) ((y_ 1) =: fn (f_ 1) (x_ 1))
        , func (f_ 2) (x ^ 2) y (tuple (x_ 1) (x_ 2)) ((y_ 2) =: fn (f_ 2) (tuple (x_ 1) (x_ 2)))
        , func (f_ 3) (x ^ 3) y (triple (x_ 1) (x_ 2) (x_ 3)) ((y_ 3) =: fn (f_ 3) (triple (x_ 1) (x_ 2) (x_ 3)))
        , vdots
        , func (f_ i) (x ^ i) y (tuplelist (x_ 1) (x_ 2) (x_ i)) ((y_ i) =: fn (f_ i) (tuplelist (x_ 1) (x_ 2) (x_ i)))
        ]


ySourceDefinition :: Note
ySourceDefinition = de $ do
    lab sourceDefinitionLabel
    let y = mathcal "Y"
    s ["An", m y <> "-" <> source', system, "is a", nS 1, "that only takes trigger inputs (with a unary alphabet) and produces, for each trigger input, an output in", m y, "based on previous output"]


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

restrictedSystemDefinition :: Note
restrictedSystemDefinition = de $ do
    let n = "n"
        sys = "S"
        x = mathcal "X"
        y = mathcal "Y"
    s ["Let", m sys, "be an", xyS x y]
    s [m $ firstOf n sys, "is the", xyS x (y ∪ setof emptyset), "that behaves like", m sys <> ", restricted to the first", m n, "inputs (and outputs)"]

environmentDefinition :: Note
environmentDefinition = de $ do
    lab deterministicEnvironmentDefinitionLabel
    lab environmentDefinitionLabel
    let x = mathcal "X"
        y = mathcal "Y"
        g = "g"
        g_ = (g !:)
        x_ = ("x" !:)
        y_ = ("y" !:)
        i = "i"
    s ["A", deterministicEnvironment, "for an", xyS x y, "(" <> "a " <> yxDE y x <> ")", "is a", constant, m $ g_ 1, "together with a", sequence, "of", functions, m $ sequ (g_ i) i, "where", m $ fun (g_ i) (y ^ (i - 1)) x]
    ma $ leftBelowEachOther $
        [ g_ 1 ∈ y
        , func (g_ 2) y x (y_ 1) ((x_ 2) =: fn (g_ 2) (y_ 1))
        , func (g_ 3) (y ^ 2) x (tuple (y_ 1) (y_ 2)) ((x_ 3) =: fn (g_ 3) (tuple (y_ 1) (y_ 2)))
        , func (g_ 4) (y ^ 3) x (triple (y_ 1) (y_ 2) (y_ 3)) ((x_ 4) =: fn (g_ 4) (triple (y_ 1) (y_ 2) (y_ 3)))
        , vdots
        , func (g_ i) (y ^ (i - 1)) x (tuplelist (y_ 1) (y_ 2) (y_ (i - 1))) ((x_ i) =: fn (g_ i) (tuplelist (y_ 1) (y_ 2) (y_ (i - 1))))
        ]

restrictedEnvironmentDefinition :: Note
restrictedEnvironmentDefinition = de $ do
    let n = "n"
        sys = "S"
        x = mathcal "X"
        y = mathcal "Y"
    s ["Let", m sys, "be an", yxE y x]
    s [m $ firstOf n sys, "is the", yxE y (x ∪ setof emptyset), "that behaves like", m sys <> ", restricted to the first", m n, "outputs"]

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
        [ x_ 1 =: g !: 1
        , y_ 1 =: f_ 1 (x_ 1)
        , x_ 2 =: g_ 2 (y_ 1)
        , y_ 2 =: f_ 2 (tuple (x_ 1) (x_ 2))
        , x_ 3 =: g_ 3 (tuple (y_ 1) (y_ 2))
        , y_ 3 =: f_ 3 (triple (x_ 1) (x_ 2) (x_ 3))
        , x_ i =: g_ i (tuplelist (y_ 1) (y_ 2) (y_ (i - 1)))
        , y_ i =: f_ i (tuplelist (x_ 1) (x_ 2) (x_ i))
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
    s [the, behaviour', m $ bhv a, "of a", xyPS xx yy, m a, "is the", sequence, "of", conditionalProbability, distributions, m $ sequ pi i, "as follows"]
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
        , fn3 (p .!: ((y !: i) .|. cs [x ^: i, y ^: (i - 1)]))
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


behaviourExamples :: Note
behaviourExamples = do
    let xx = mathcal "X"
        yy = mathcal "Y"
        q = "Query"
    let p = "p"
    let s_ = ("S" !:)
        sp = s_ p
    let i = "i"
    let n = "n"
        bot = "E"
        yy' = yy ∪ setof bot
    let v = "v"
        v1 = v !: 1
        v2 = v !: 2
        vi = v !: i
        vn = v !: n
    let x = "x"
        x1 = x !: 1
        x2 = x !: 2
        xi = x !: i
        xim = x !: (i - 1)
    let y = "y"
        y1 = y !: 1
        y2 = y !: 2
        yi = y !: i
        yim = y !: (i - 1)
    let z = "Z"
        z1 = z !: 1
        z2 = z !: 2
        zi = z !: i
        zim = z !: (i - 1)
        zn = z !: n
    let t = "t"
        tv = t !: v
        tvi = tv !: i
    let tt = "T"
        tt_ = fn tt
    ex $ do
        s ["Let", m $ xx =: setof q, and, m $ yy =: setofs [0, 1], be, sets, "and let", m $ p ∈ ccint 0 1]
        s ["Consider the", xyS xx yy, m sp, "that, on each input, outputs a bit that is", m 1, with, probability, m p]
        s ["That is to say, ", m sp, "has the following", behaviour]
        ma $ bhvsi_ sp i =: cases (do
              p       & (y !: i) =: 1
              lnbk
              (1 - p) & (y !: i) =: 0
            )
        s ["We will now describe a", randomVariable, "over the", set, "of", xyDSs xx yy', "(a", xyPS xx yy <> ")", "that has the", behaviour, "of", m $ firstOf n sp]

        s ["First we have to describe the", set, "to build this", randomVariable, "over"]
        s ["Let", m $ v =: veclist v1 v2 vn ∈ bitss n, "be a random", vector, "of bits"]
        s ["Now consider the", xyDS xx yy', m tv, "defined as the", sequence, "of", functions, m $ sequ tvi i, "as follows"]
        ma $ fn tvi (tuplelist x1 x2 xi) =: cases (do
            vi & i <= n
            lnbk
            bot & i > n
            )
        s ["Let", m $ list z1 z2 zn, be, independent, and, identicallyDistributed, randomVariables, over, m bits, "such that", m $ fa (i ∈ setlist 1 2 n) (prob (zi =: 1) =: p), and, m $ fa (i ∈ setlist 1 2 n) (prob (zi =: 0) =: 1 - p), "hold"]
        s ["We now define the", randomVariable, m tt, over, m $ setcmpr tv (v ∈ bitss n), "as follows"]
        ma $ tt =: t !: tuplelist z1 z2 zn


        s [m tt, "is now a", xyPS xx yy']
        s ["Note that", m $ tt_ (tuplelist x1 x2 xi) =: zi, "holds for", m $ i <= n, and, m $ tt_ (tuplelist x1 x2 xi) =: bot, "otherwise"]

        s ["Now we can prove that", m tt, "does in fact have the correct", behaviour, "as follows"]
        proof $ do
            aligneqs (bhvsi_ tt i)
                [ cprob (tt_ (x ^ i) =: yi) (list (tt_ x1 =: y1) (tt_ (tuple x1 x2) =: y2) (tt_ (x ^ (i - 1)) =: yim))
                , cprob (zi =: yi) (list (z1 =: y1) (y2 =: y2) (zim =: yim))
                , prob (zi =: yi)
                , cases $ do
                      p       & (y !: i) =: 1
                      lnbk
                      (1 - p) & (y !: i) =: 0
                ]
            s ["Clearly, ", m $ bhvs tt i bot (x ^ i) (y ^ (i - 1)), " is zero for", m $ i <= n, "and one otherwise"]
            s ["We can therefore conclude that", m tt, "has the", behaviour, "of", m $ firstOf n sp]

        let a = alpha
        s ["Next, we describe a deterministic", converter, m a, "such that the following holds"]
        let ssq = s_ $ 1 /: sqrt 2
            ssh = s_ $ 1 /: 2
        ma $ conv_ a (firstOf n ssq) =: firstOf (n /: 2) ssh
        s ["Observe that the", probability, "that two consequtive bits output by", m ssq, "are both equal to", m 1, "is", m $ (1 /: sqrt 2) * (1 /: sqrt 2) =: (1 /: 2)]
        s ["The idea is to define the", converter, m a, "such that for every query at its outside", interface <> ", it fetches two bits at the inside", interface, "and outputs", m 1, "at the outside", interface, "if the two bits are both equal to", m 1, and, m 0, "in the other three cases"]

        let o_ = text "out"
            i_ = text "in"
            oq = tuple o_ q
            iq = tuple i_ q
            o0 = tuple o_ 0
            o1 = tuple o_ 1
            i0 = tuple i_ 0
            i1 = tuple i_ 1
            ob = tuple o_ bot
            ib = tuple i_ bot
            wsi = setofs [oq, i0, i1, ib] -- Weird set in
            wso = setofs [o0, o1, ob, iq] -- Weird set out
        s ["We model the", converter, "as a", xyDS wsi wso, "that takes tuples where the first element specifies whether the second element arrived at the inside or the outside", interface, "and produces tuples where the first element specifies whether the second element is output at the inside or the outside", interface]
        let ai = a !: i
        s ["Concretely we have to define the", sequence, "of", functions, m $ sequ ai i, "that defines the workings of", m a, "as follows"]
        ma $ fun ai (wsi ^ i) wso
        itemize $ do
            item $ do
                s ["The first output is specified as follows"]
                let a1 = fn (a !: 1)
                ma $ leftBelowEachOther
                    [ a1 oq =: iq
                    , a1 unmatched =: ob
                    ]
                s ["That is, when queried (which we conveniently model as", m oq <> ")", "it will query at the inside", interface, "(which we model as", m iq <> ")"]
                s ["If anything other than a query comes in, we output an error", "(" <> m ob <> ")"]
            item $ do
                s ["For", m $ i >= 2, "we set", m $ fn ai (tuplelist x1 x2 xim), "to", m ob, "if any of the", m xi, "are", m ob]
                s ["This models the fact that once the", system, "errors, it will error every time it's called subsequently"]
            item $ do
                s ["On the other hand, if none of", m $ list x1 x2 xim, "are", m ob <> ", we distinguish three cases based on", m $ i `mod` 3]
                itemize $ do
                    item $ do
                        s ["For", m $ i `mod` 3 =: 1, "we just have", m a, "query the inside", interface, "and error otherwise"]
                        ma $ leftBelowEachOther
                            [ fn ai (list unmatched unmatched oq) =: iq
                            , fn ai (list unmatched unmatched unmatched) =: ob
                            ]
                    item $ do
                        s ["For", m $ i `mod` 3 =: 2, "we just have", m a, "query the inside", interface, "again and error if anything happens other than an the receival of an answer at the inside", interface]
                        ma $ leftBelowEachOther
                            [ fn ai (list unmatched unmatched i0) =: iq
                            , fn ai (list unmatched unmatched i1) =: iq
                            , fn ai (list unmatched unmatched unmatched) =: ob
                            ]
                    item $ do
                        s ["For", m $ i `mod` 3 =: 0, "let", m a, "finally use the previously gotten bits"]
                        ma $ leftBelowEachOther
                            [ fn ai (listofs [unmatched, unmatched, dotsc, i1, i1]) =: o1
                            , fn ai (listofs [unmatched, unmatched, dotsc, i0, i1]) =: o0
                            , fn ai (listofs [unmatched, unmatched, dotsc, i1, i0]) =: o0
                            , fn ai (listofs [unmatched, unmatched, dotsc, i0, i0]) =: o0
                            , fn ai (list unmatched unmatched unmatched) =: ob
                            ]
                        s ["We have", m a, "output", m 1, "if the previous two input bits were", m 1, and, m 0, "otherwise"]
            s ["Now,", m $ firstOf n ssq, "will output", m bot, "after", m n, "queries"]
            s ["As per the construction,", m a, "will query", m $ firstOf n ssq, m 2, "times for every query it gets, and will therefore output", m bot, "after", m $ n /: 2, "queries"]
            s ["This means that the construction of", m $ firstOf (n /: 2) ssh, from, m $ firstOf n ssq, "with the", converter, m a]




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
        (.|.) a b = a <> mid <> b
    s [the, behaviour', m $ bhv e, "of a", yxPE yy xx, m e, "is the", sequence, "of", conditionalProbability, distributions, m $ sequ pi i, "as follows"]
    let x_ i = "x" !: i
        y_ i = "y" !: i
        g i n = fn ("g" .^: e .!: i) (cs n)
    ma $ belowEachOther [LeftColumn, LeftColumn]
        [ fn (p .!: ((x !: 1)))
                (x_ 1)
             & "" =: prob (("g" .^: e .!: 1) =: x_ 1)
        , fn3 (p .!: ((x !: 2) .|. cs [x !: 1, y !: 1]))
                (x_ 2)
                (x_ 1)
                (y_ 1)
             & "" =: cprob (g 2 [y_ 1] =: x_ 2)
                           (("g" .^: e .!: 1) =: x_ 1)
        , fn3 (p .!: ((x !: 3) .|. cs [tuple (x !: 1) (x !: 2), tuple (y !: 1) (y !: 2)]))
                (x_ 3)
                (tuple (x_ 1) (x_ 2))
                (tuple (y_ 1) (y_ 2))
             & "" =: cprob (g 3 [y_ 1, y_ 2] =: x_ 3)
                           (cs [("g" .^: e .!: 1) =: x_ 1, g 2 [y_ 1] =: x_ 2])
        , "" & vdots
        , fn3 (p .!: ((x !: i) .|. cs [x ^ (i - 1), y ^ (i - 1)]))
              (x_ i)
              ("y" ^ (i - 1))
              ("x" ^ (i - 1))
             & "" =: cprob (g i ["y" ^ (i - 1)] =: x_ i)
                           (cs [("g" .^: e .!: 1) =: x_ 1, g 2 [y_ 1] =: x_ 2, g 3 [y_ 1, y_ 2] =: x_ 3, g (i - 1) ["y" ^ (i - 2)] =: "x" !: (i - 1)])
        , "" & vdots
        ]
    s ["Note that we use", m $ "x" ^ i, "as an abbreviaton for", m $ cs [x_ 1, x_ 2, dotsc, x_ i] <> ",", m $ "y" ^ i, "for", m $ cs [y_ 1, y_ 2, dotsc, y_ i] ,"as well as", m $ x ^ i, "for", m $ cs [x !: 1, x !: 2, dotsc, x !: i]]

equivalentProbabillisticEnvironments :: Note
equivalentProbabillisticEnvironments = de $ do
    let x = mathcal "X"
        y = mathcal "Y"
    s ["Two", yxPEs y x, "are", defineTerm "equivalent", "if they have the same", behaviour]


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

