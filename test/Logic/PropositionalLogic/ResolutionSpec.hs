module Logic.PropositionalLogic.ResolutionSpec (spec) where

import           Prelude

import           Control.Monad                       (replicateM)
import           Data.Text.Arbitrary
import           Test.Hspec
import           Test.QuickCheck
import           Test.QuickCheck.Checkers
import           Test.QuickCheck.Classes             (monoid)
import           TestUtils                           (batch)

import           Logic.PropositionalLogic.Resolution

instance EqProp CNFSentence where
    (=-=) = eq

instance Arbitrary CNFSentence where
    arbitrary = scale (const 5) $ sized go
      where
        go :: Int -> Gen CNFSentence
        go n = Conjunction <$> replicateM n arbitrary

instance EqProp Disjunction where
    (=-=) = eq

instance Arbitrary Disjunction where
    arbitrary = scale (const 5) $ sized go
      where
        go :: Int -> Gen Disjunction
        go n = Disjunct <$> replicateM n arbitrary

instance Arbitrary CNFLit where
    arbitrary = oneof [
                        JustLit <$> arbitrary
                      , NotLit <$> arbitrary
                      ]


spec :: Spec
spec = do
    describe "CNFSentence" $ do
        batch "is a Monoid" $ monoid (undefined :: CNFSentence)
    describe "Disjunction" $ do
        batch "is a Monoid" $ monoid (undefined :: Disjunction)

