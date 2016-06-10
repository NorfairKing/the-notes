module TH.Literal where

import           Prelude

import           Types
import           Utils

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (sequenceQ)


makeStrs :: [String] -> Q [Dec]
makeStrs ns = fmap concat $ sequenceQ $ map makeStr ns

makeStr :: String -> Q [Dec]
makeStr n = makeAbbr n n

makeAbbrs :: [(String, String)] -> Q [Dec]
makeAbbrs abrs = fmap concat $ sequenceQ $ map (uncurry makeAbbr) abrs

makeAbbr :: String -> String -> Q [Dec]
makeAbbr abr str = return [sig, fun]
  where
    name = mkName . camelCase . sanitize $ abr
    sig = SigD name (ConT ''Note)
    fun = FunD name
            [ Clause
                []
                (NormalB . LitE . StringL $ str)
                []
            ]

makeIxs :: [String] -> Q [Dec]
makeIxs ns = fmap concat $ sequenceQ $ map makeIx ns

makeIx :: String -> Q [Dec]
makeIx str = return [sig, fun]
  where
    name = mkName . camelCase . sanitize $ str
    sig = SigD name (ConT ''Note)
    fun = FunD name
            [ Clause
                []
                (NormalB $ AppE (VarE $ mkName "ix") $ LitE $ StringL $ str)
                []
            ]
