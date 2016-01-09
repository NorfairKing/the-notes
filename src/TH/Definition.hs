module TH.Definition (
      makeDef
    , makeDefs
    ) where

import           Types
import           Utils

import           Prelude                    (Char, concat, concatMap, fmap, map,
                                             return)

import           Data.Char                  (toLower, toUpper)
import           Data.List                  (intercalate)

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (sequenceQ)

import           TH.Label

makeDefs :: [String] -> Q [Dec]
makeDefs strs = fmap concat $ sequenceQ $ map makeDef strs

makeDef :: String -> Q [Dec]
makeDef concept = do
    labDecs <- makeDe concept
    return $ labDecs ++ [termSig, termFun, indexSig, indexFun, refSig, refFun]
  where
    baseName :: String
    baseName = camelCase $ sanitize concept

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

    definitionName :: Name
    definitionName = mkName "Definition"

    labelConceptLit :: Exp
    labelConceptLit = LitE $ StringL $ kebabCase $ sanitize concept

    labelSig :: Dec
    labelSig = SigD labelDefName (ConT ''Label)

    labelFun :: Dec
    labelFun = FunD labelDefName [Clause [] (NormalB $ AppE (AppE (ConE 'MkLabel) (ConE definitionName)) labelConceptLit) []]

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

