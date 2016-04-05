module Cryptography.SystemAlgebra.DiscreteSystems where

import           Notes                                            hiding
                                                                   (cyclic)

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Basics.Terms
import           Functions.BinaryOperation.Macro
import           Functions.BinaryOperation.Terms
import           Probability.ConditionalProbability.Macro
import           Probability.ConditionalProbability.Terms
import           Probability.Independence.Terms
import           Probability.ProbabilityMeasure.Macro
import           Probability.RandomVariable.Terms
import           Relations.Domain.Terms
import           Sets.Basics.Terms

import           Cryptography.SymmetricCryptography.Macro

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

