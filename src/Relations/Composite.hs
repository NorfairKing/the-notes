module Relations.Composite (compositeRelations) where

import           Notes

compositeRelations :: Notes
compositeRelations = notesPart "compositeRelations" body

body :: Note
body = do
  section "Composite relations"

  compositeRelationDefinition

compositeRelationDefinition :: Note
compositeRelationDefinition = de $ do
    s ["Let ", m q, and, m r, " be two binary relations"]
    s ["The composition of ", m q, with, m r, " (read ", dquoted (m q <> " after " <> m r), ") is the following relation"]

    ma $ q ● r === setcmpr (tuple a b) (te c $ (pars $ tuple a c ∈ r) ∧ (pars $ tuple c b ∈ q))

  where
    q = "Q"
    r = "R"
    a = "a"
    b = "b"
    c = "c"

-- TODO associativity
-- TODO distributivity with inverse
-- TODO domain after composition
-- TODO image after composition
-- TODO if the image of the second is a part of the domain of the first, then the domain of the composition is the domain of the second. really? sure? make sure to prove it!
