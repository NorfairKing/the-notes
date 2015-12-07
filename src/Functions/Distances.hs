module Functions.Distances where

import           Notes

import           Functions.Application.Macro
import           Functions.Basics.Macro
import           Functions.Distances.Macro

makeDefs [
      "distance"
    , "pseudometric"
    , "metric"

    , "Jaccard similarity"
    , "Jaccard distance"
    ]

distances :: Notes
distances = notesPart "distances" $ do
    section "Distances"

    subsection "Pseudometrics"
    distanceDefinition
    distanceExamples
    jaccardSimilarityDefinition
    jaccardSimilarityEquivalentDefinition

    subsection "Metrics"
    metricDefinition
    metricExamples

distanceDefinition :: Note
distanceDefinition = de $ do
    lab distanceDefinitionLabel
    lab pseudometricDefinitionLabel
    s ["Let ", m ss, " be a set"]
    s ["A ", term "distance function", " ", m d, " for ", m ss, " is a function ", m (fun d tups realsp), " with the following four properties"]
    enumerate $ do
      item $ m $ fa rxy $ dxy =: 0
      item $ m $ fa rxy $ dxy =: dyx
      item $ do
        s ["The ", term "triangle inequality"]
        ma $ fa (cs [x, y, z] ∈ reals) $ (d `fn` xy + d `fn` yz) <= (d `fn` xz)
    s ["A distance function is also called a ", term "pseudometric"]
  where
    x = "x"
    y = "y"
    z = "z"
    xy = cs [x, y]
    yx = cs [y, x]
    yz = cs [y, z]
    xz = cs [x, z]
    dxy = d `fn` xy
    dyx = d `fn` yx
    rxy = xy ∈ tups
    d = dist_
    ss = "S"
    tups = ss `setprod` ss

distanceExamples :: Note
distanceExamples = do
    ex $ do
        s [the, term "cosine distance"]
        s ["Let ", m q, " be a natural numbers"]
        ma $ func2 cd rq rq realsp v w $ arccos_ $ (trans v * w) /: (n2 v * n2 w)

        toprove_ "Prove that this is actually a distance"

  where
    q = "q"
    v = "v"
    cd = dist_ !: "cos"
    n2 = norm_ 2
    w = "w"
    rq = realVecSpace q


jaccard :: Note -> Note -> Note
jaccard n m = "J" `fn` cs [n,m]

jaccardSimilarityDefinition :: Note
jaccardSimilarityDefinition = do
  de $ do
    lab jaccardSimilarityDefinitionLabel
    s ["The ", jaccardSimilarity', " of two sets ", m a, " and ", m b, " is defined as ", m (jaccard a b)]
    ma $ jaccard a b === (setsize (a ∩ b) / setsize (a ∪ b))
  de $ do
    lab jaccardDistanceDefinitionLabel
    s ["The ", jaccardDistance', " ", m dj, " between two sets ", m a, " and ", m b, " is defined as ", m (jaccard a b - 1)]
    ma $ dj `fn` cs [a, b] === (jaccard a b - 1)

  todo "prove that the Jaccard distance is in fact a distance"

  where
    a = "A"
    b = "B"
    dj = "d" !: "J"

jaccardSimilarityEquivalentDefinition :: Note
jaccardSimilarityEquivalentDefinition = thm $ do
  s ["Let ", m a, " and ", m b, " be sets"]
  s ["The ", jaccardSimilarity, " of ", m a, " and ", m b, " is equal to the following expression"]

  ma $ setsize (a ∩ b) / ((setsize $ a `setdiff` b) + (setsize $ b `setdiff` a) + (setsize $ a ∩ b))

  toprove
  where
    a = "A"
    b = "B"


metricDefinition :: Note
metricDefinition = de $ do
  lab metricDefinitionLabel
  s ["A ", metric', " on a set ", m ss, " is a distance function", ref distanceDefinitionLabel, " ", m metr_, " on that set with one extra property"]
  ma $ fa (cs [v,w] ∈ ss) (d_ v w =: 0 ⇔ v =: w)

  where
    v = "v"
    w = "w"
    ss = "S"
    d_ = distapp metr_


metricExamples :: Note
metricExamples = do
  ex $ do
    s [the, m lp, "-", metric, "s"]
    s ["Let ", m p, " be a real number and ", m q, " a natural numbers"]
    ma $ func2 lp rq rq realsp v w $ nrt p $ sumcmpr (i =: 1) q $ (pars $ v_ i - w_ i) ^: p

    toprove_ "Prove that these are actually metrics"

  ex $ do
    s [the, m lif, "-", metric]
    ma $ func2 lif rq rq realsp v w $ max i $ av $ v_ i - w_ i

    toprove_ "Prove that this is actually a metric"

  where
    i = "i"
    l = "L"
    p = "p"
    q = "q"
    v = "v"
    v_ n = v !: n
    w = "w"
    w_ n = w !: n
    rq = realVecSpace q
    lp = l !: p
    lif = l !: infty


