{-# LANGUAGE CPP #-}
module Logic.PropositionalLogic.TruthTablesSpec (spec) where

import           Prelude

import           Test.Hspec
import           Test.QuickCheck

import           Data.Text                            (Text)
import qualified Data.Text                            as T
import           Data.Text.Arbitrary

import           Logic.PropositionalLogic.TruthTables


-- instance EqProp Sentence where
    -- (=-=) = eq

instance Arbitrary Sentence where
    -- The const 5 size parameter ensures that the sentence doesn't get too big.
    arbitrary = scale (const 5) $ sized go
      where
        go :: Int -> Gen Sentence
        go 0 = oneof
                [
                  Lit <$> arbitrary
                , Symbol <$> arbitrary
                ]
        go 1 = oneof
                [
                  Lit <$> arbitrary
                , Symbol <$> arbitrary
                , Not <$> go 0
                ]
        go n = oneof
                [
                  Lit <$> arbitrary
                , Symbol <$> arbitrary
                , Not <$> go (n-1)
                , Or <$> go (n-1) <*> go (n-1)
                , And <$> go (n-1) <*> go (n-1)
                , Implies <$> go (n-1) <*> go (n-1)
                , Equiv <$> go (n-1) <*> go (n-1)
                ]

    shrink s = ss ++ concatMap shrink ss
      where
        ss = subExprs s


spec :: Spec
spec = do
    describe "isBinary" $ do
        it "is true for binary operators" $ do
            isBinary (And (Lit True) (Lit False)) `shouldBe` True
            isBinary (Or (Lit True) (Lit False))  `shouldBe` True

    describe "subExprs" $ do
        it "returns 2 for binary operators" $ do
            property $ \s -> isBinary s ==> (length (subExprs s) == 2)

    describe "removeEquivs" $ do
        it "leaves no Equivs" $ do
            property $ \s -> hasEquivs s ==> not (hasEquivs $ removeEquivs s)
        validTransformation removeEquivs

    describe "removeImplies" $ do
        it "leaves no Implies" $ do
            property $ \s -> hasImplies s ==> not (hasImplies $ removeImplies s)
        validTransformation removeImplies

    describe "undoNotNots" $ do
        it "leaves no NotNots" $ do
            property $ \s -> hasNotNots s ==> not (hasNotNots $ undoNotNots s)
        validTransformation undoNotNots

    describe "slideDownTopNots" $ do
        validTransformation slideDownTopNots

    describe "distributeOr" $ do
        validTransformation distributeOrs

    describe "isCNF" $ do
        it "works on simple testcases" $ do
            (Lit True) `shouldSatisfy` isCNF
            (Lit False) `shouldSatisfy` isCNF
            (Or (Lit True) (Lit False)) `shouldSatisfy` isCNF
            (And (Lit True) (Lit False)) `shouldSatisfy` isCNF
            (Implies (Lit True) (Lit False)) `shouldNotSatisfy` isCNF
            (Equiv (Lit True) (Lit False)) `shouldNotSatisfy` isCNF

    describe "cnfTransform" $ do
        validTransformation cnfTransform
        it "transforms a sentence into CNF" $ do
            property $ isCNF . cnfTransform

    describe "symbolsOf" $ do
        it "works on simple testcases" $ do
            symbolsOf (Equiv (Symbol "a") (And (Symbol "b") (Symbol "c"))) `shouldBe` ["a", "b", "c"]
            symbolsOf (Not (Lit True)) `shouldBe` []

    describe "possibleStates" $ do
        it "has an exponential space complexity" $ do
            property $ \s -> 2 ^ (length $ symbolsOf s) === (length $ possibleStates $ symbolsOf s)


evaluatable :: Sentence -> Bool
evaluatable = not . mapHas go
  where
    go (Symbol _) = True
    go _ = False

validTransformation :: (Sentence -> Sentence) -> Spec
validTransformation f = it "is a valid transformation" $ property $ \s -> evaluatable s ==> ((evaluate s) === (evaluate (f s)))





