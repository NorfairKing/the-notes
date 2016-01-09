module Logic.PropositionalLogic.SentenceSpec (spec) where

import           Prelude

import           Test.Hspec
import           Test.QuickCheck

import           Data.List                         (nub)
import           Data.Text                         (Text)
import qualified Data.Text                         as T
import           Data.Text.Arbitrary

import           Logic.PropositionalLogic.Sentence

instance Arbitrary Literal where
    arbitrary = oneof
        [
          Lit <$> arbitrary
        , Symbol <$> arbitrary
        ]


instance Arbitrary Sentence where
    -- The const 5 size parameter ensures that the sentence doesn't get too big.
    arbitrary = scale (const 5) $ sized go
      where
        go :: Int -> Gen Sentence
        go 0 = Literal <$> arbitrary
        go 1 = oneof
                [
                  Literal <$> arbitrary
                , Not <$> go 0
                ]
        go n = oneof
                [
                  Literal <$> arbitrary
                , Not <$> go (n-1)
                , Or <$> go (n-1) <*> go (n-1)
                , And <$> go (n-1) <*> go (n-1)
                , Implies <$> go (n-1) <*> go (n-1)
                , Equiv <$> go (n-1) <*> go (n-1)
                ]

    shrink s = ss ++ concatMap shrink ss
      where ss = subExprs s


spec :: Spec
spec = do
    describe "isBinary" $ do
        it "is true for binary operators" $ do
            let t = Literal $ Lit True
                f = Literal $ Lit False
            And t f     `shouldSatisfy` isBinary
            Or t f      `shouldSatisfy` isBinary
            Implies t f `shouldSatisfy` isBinary
            Equiv t f   `shouldSatisfy` isBinary

    describe "subExprs" $ do
        it "has length 2 for binary operators" $ do
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
            let t = Literal $ Lit True
                f = Literal $ Lit False
            t `shouldSatisfy` isCNF
            f `shouldSatisfy` isCNF
            (Or t f) `shouldSatisfy` isCNF
            (And t f) `shouldSatisfy` isCNF
            (Implies t f) `shouldNotSatisfy` isCNF
            (Equiv t f) `shouldNotSatisfy` isCNF

    describe "cnfTransform" $ do
        validTransformation cnfTransform
        it "transforms a sentence into CNF" $ do
            property $ isCNF . cnfTransform

    describe "symbolsOf" $ do
        it "works on simple testcases" $ do
            let t = Literal $ Lit True
                s = Literal . Symbol
            symbolsOf (Equiv (s "a") (And (s "b") (s "c"))) `shouldBe` ["a", "b", "c"]
            symbolsOf (Not t) `shouldBe` []
        it "returns a list of unique symbols (a set)" $ do
            property $ \s -> symbolsOf s == nub (symbolsOf s)

    describe "possibleStates" $ do
        it "has an exponential space complexity" $ do
            property $ \s -> 2 ^ (length $ symbolsOf s) === (length $ possibleStates $ symbolsOf s)


evaluatable :: Sentence -> Bool
evaluatable = not . mapHas go
  where
    go (Literal (Symbol _)) = True
    go _ = False

validTransformation :: (Sentence -> Sentence) -> Spec
validTransformation f = it "is a valid transformation" $ property $ \s -> evaluatable s ==> ((evaluate s) === (evaluate (f s)))





