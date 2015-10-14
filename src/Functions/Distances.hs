module Functions.Distances (distances) where

import           Notes

distances :: Notes
distances = notesPart "distances" body

body :: Note
body = do
  distanceDefinition
  jaccardSimilarity
  jaccardSimilarityEquivalentDefinition

distanceDefinition :: Note
distanceDefinition = de $ do
  s ["Let ", m ss, " be a set"]
  s ["A ", term "distance function", " ", m d, " for ", m ss, " is a function ", m (fun d tups realsp), " with the following four properties"]
  enumerate $ do
    item $ m $ fa rxy $ dxy =: 0
    item $ m $ fa rxy $ dxy =: dyx
    item $ do
      s ["The ", term "triangle inequality"]
      ma $ fa (cs [x, y, z] ∈ reals) $ (d `fn` xy + d `fn` yz) <= (d `fn` xz)

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
    d = "d"
    ss = "S"
    tups = ss `setprod` ss

jaccard :: Note -> Note -> Note
jaccard n m = "J" `funapp` cs [n,m]

jaccardSimilarity :: Note
jaccardSimilarity = do
  de $ do
    s ["The ", term "Jaccard similarity", " of two sets ", m a, " and ", m b, " is defined as ", m (jaccard a b)]
    ma $ jaccard a b === (setsize (a ∩ b) / setsize (a ∪ b))
  de $ do
    s ["The ", ix "Jaccard distance", " ", m dj, " between two sets ", m a, " and ", m b, " is defined as ", m (jaccard a b - 1)]
    ma $ dj `fn` cs [a, b] === (jaccard a b - 1)

  where
    a = "A"
    b = "B"
    dj = "d" !: "J"

jaccardSimilarityEquivalentDefinition :: Note
jaccardSimilarityEquivalentDefinition = thm $ do
  s ["Let ", m a, " and ", m b, " be sets"]
  s ["The ", ix "Jaccard similarity", " of ", m a, " and ", m b, " is equal to the following expression"]

  ma $ setsize (a ∩ b) / ((setsize $ a `setdiff` b) + (setsize $ b `setdiff` a) + (setsize $ a ∩ b))

  toprove
  where
    a = "A"
    b = "B"
