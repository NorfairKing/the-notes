module Relations.Basics (
    relationBasics

  , relation
  ) where

import           Notes

relationBasics :: Notes
relationBasics = notesPart "basics" body

body :: Note
body = do
  section "Basics"

  relationDefinition
  binaryRelationDefinition
  ternaryRelationDefinition
  unitRelationDefinition
  inverseRelationDefinition

relation :: Note
relation = ix "relation"

relationDefinition :: Note
relationDefinition = de $ do
    s ["A ", term "relation", " between ", m n, " sets ", m $ cs [x 1, x 2, dotsc, x n], " is a subset of their Carthesian product"]
  where
    n = "n"
    x i = "X" !: i

binaryRelationDefinition :: Note
binaryRelationDefinition = de $ do
  s ["A binary ", relation, " " , m rel, " is a relation between two sets"]
  s ["If a binary relation ", m rel, " between sets ", m a, and, m b, " contains a tuple ", m $ tuple v w, " then that is often denoted as ", m $ inrel v w]
  where
    a = "A"
    b = "B"
    v = "v"
    w = "w"

ternaryRelationDefinition :: Note
ternaryRelationDefinition = de $ s ["A ternary ", relation, " is a relation between three sets"]

unitRelationDefinition :: Note
unitRelationDefinition = de $ do
    s ["Let ", m x, " be a set"]
    s ["The ", m n, "-ary ", term "unit relation", " ", m (relunit_ n), " is the set of all tuples of the same element"]
    ma $ relunit_ 2 === setcmpr (tuple v v) (v ∈ x)
    ma $ relunit_ n === setcmpr (pars $ list v v v) (v ∈ x)
  where
    x = "X"
    v = "v"
    n = "n"

inverseRelationDefinition :: Note
inverseRelationDefinition = de $ do
    s ["Let ", m rel, " be a binary relation on the sets ", m a, and, m b]
    s [the, term "inverse relation", " ", m (relinv rel), " of ", m rel, " is the following relation"]
    ma $ relinv rel === setcmpr (tuple y x) (tuple x y ∈ rel)
  where
    a = "A"
    b = "B"
    x = "x"
    y = "y"

-- TODO inverse of inverse is normal again

