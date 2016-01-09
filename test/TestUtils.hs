module TestUtils where

import           Prelude

import           Control.Monad            (forM_)

import           Test.Hspec
import           Test.QuickCheck
import           Test.QuickCheck.Checkers
import           Test.QuickCheck.Classes  (monoid)

-- Recall:
-- type TestBatch = (String, [Test])
-- type Test = (String, Property)
batch :: String -> TestBatch -> Spec
batch str (name, ts) =
    describe str $
            forM_ ts $ \(tname, p) ->
                        it tname $ property p


