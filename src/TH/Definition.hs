module TH.Definition (
      makeDef
    , makeDefs
    ) where

import           Types

import           Prelude                    (concat, fmap, map, return)

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (sequenceQ)

makeDefs :: [String] -> Q [Dec]
makeDefs strs = fmap concat $ sequenceQ $ map makeDef strs

makeDef :: String -> Q [Dec]
makeDef concept = return $ [termSig, termFun, indexSig, indexFun, labelSig, labelFun, refSig, refFun]
  where
    noteName :: Name
    noteName = mkName "Note"

    termName :: Name
    termName = mkName $ concept ++ "'"

    termSig :: Dec
    termSig = SigD termName (ConT noteName)

    termFun :: Dec
    termFun = FunD termName [Clause [] (NormalB $ AppE (VarE $ mkName "term") (LitE $ StringL concept)) []]

    indexName :: Name
    indexName = mkName concept

    indexSig :: Dec
    indexSig = SigD indexName (ConT noteName)

    indexFun :: Dec
    indexFun = FunD indexName [Clause [] (NormalB $ AppE (VarE $ mkName "ix") (LitE $ StringL concept)) []]

    labelDefName :: Name
    labelDefName = mkName $ concept ++ "DefinitionLabel"

    labelName :: Name
    labelName = mkName "Label"

    definitionName :: Name
    definitionName = mkName "Definition"

    labelSig :: Dec
    labelSig = SigD labelDefName (ConT labelName)

    labelFun :: Dec
    labelFun = FunD labelDefName [Clause [] (NormalB $ (AppE (AppE (ConE labelName) (ConE definitionName)) (LitE $ StringL concept))) []]

    refName :: Name
    refName = mkName $ concept ++ "_"

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

