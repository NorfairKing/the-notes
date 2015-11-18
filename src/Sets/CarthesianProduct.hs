module Sets.CarthesianProduct (
          carthesianProducts

        , carthesianProduct, carthesianProduct_, carthesianProductDefinitionLabel
    ) where

import           Notes

makeDefs ["Carthesian product"]

carthesianProducts :: Notes
carthesianProducts = notesPart "carthesian-products" body

body :: Note
body = do
    carthesianProductDefinition

carthesianProductDefinition :: Note
carthesianProductDefinition = de $ do
    lab carthesianProductDefinitionLabel
    s [the, carthesianProduct', " of two sets ", m a, and, m b, " is the set of all tuples of elements in ", m a, and, m b, " respectively "]
    ma $ setcmpr (tuple x y) $ x ∈ a ∧ y ∈ b
  where
    a = "A"
    b = "B"
    x = "x"
    y = "y"
