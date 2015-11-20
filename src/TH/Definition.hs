module TH.Definition (
      makeDef
    , makeDefs
    ) where

import           Types

import           Prelude                    (Char, concat, fmap, map, return)

import           Data.Char                  (toLower, toUpper)
import           Data.List                  (intercalate)

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (sequenceQ)

makeDefs :: [String] -> Q [Dec]
makeDefs strs = fmap concat $ sequenceQ $ map makeDef strs

makeDef :: String -> Q [Dec]
makeDef concept = return $ [termSig, termFun, indexSig, indexFun, labelSig, labelFun, refSig, refFun]
  where
    baseName :: String
    baseName = constructName concept

    conceptLit :: Exp
    conceptLit = LitE $ StringL concept

    noteName :: Name
    noteName = mkName "Note"

    termName :: Name
    termName = mkName $ baseName ++ "'"

    termSig :: Dec
    termSig = SigD termName (ConT noteName)

    termFun :: Dec
    termFun = FunD termName [Clause [] (NormalB $ AppE (VarE $ mkName "term") conceptLit) []]

    indexName :: Name
    indexName = mkName baseName

    indexSig :: Dec
    indexSig = SigD indexName (ConT noteName)

    indexFun :: Dec
    indexFun = FunD indexName [Clause [] (NormalB $ AppE (VarE $ mkName "ix") conceptLit) []]

    labelDefName :: Name
    labelDefName = mkName $ baseName ++ "DefinitionLabel"

    labelName :: Name
    labelName = mkName "Label"

    definitionName :: Name
    definitionName = mkName "Definition"

    labelConceptLit :: Exp
    labelConceptLit = LitE $ StringL $ interdashed concept

    labelSig :: Dec
    labelSig = SigD labelDefName (ConT labelName)

    labelFun :: Dec
    labelFun = FunD labelDefName [Clause [] (NormalB $ (AppE (AppE (ConE labelName) (ConE definitionName)) labelConceptLit)) []]

    refName :: Name
    refName = mkName $ baseName ++ "_"

    refSig :: Dec
    refSig = SigD refName (ConT noteName)

    refFun :: Dec
    refFun = FunD
                refName
                [
                  Clause
                    [] -- No arguments
                    (
                      NormalB $
                        AppE
                          (AppE
                            (VarE $ mkName "mappend")
                            (VarE indexName))
                          (AppE
                            (VarE $ mkName "ref")
                            (VarE labelDefName))
                    )
                    [] -- No wheres
                ]

constructName :: String -> String
constructName = camelCase . sanitize

sanitize :: String -> String
sanitize = map replaceBad
  where
    replaceBad :: Char -> Char
    replaceBad '-' = ' '
    replaceBad c = c

camelCase :: String -> String
camelCase str = (\(s:ss) -> (toLower s):ss) $ concat $ map (\(s:ss) -> (toUpper s) : ss) $ words str

interdashed :: String -> String
interdashed str = intercalate "-" $ words $ map toLower str
