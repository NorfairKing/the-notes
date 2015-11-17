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
makeDef str = return $ indexDef str ++ refDef str ++ labelDef str

noteName :: Name
noteName = mkName "Note"

indexDef :: String -> [Dec]
indexDef concept = [sig, fun]
  where
    name = mkName concept
    sig  = SigD
            name
            (ConT noteName)
    fun  = FunD
            name
            [
              Clause
                [] -- No arguments
                (
                  NormalB $
                    AppE
                      (VarE $ mkName "ix")
                      (LitE $ StringL concept)
                )
                [] -- No wheres
            ]

refDef :: String -> [Dec]
refDef concept = [sig, fun]
  where
    name = mkName $ concept ++ "_"
    defLabelName = mkName $ concept ++ "DefinitionLabel"
    sig = SigD
            name
            (ConT noteName)
    fun = FunD
            name
            [
              Clause
                [] -- No arguments
                (
                  NormalB $
                    AppE
                      (AppE
                        (VarE $ mkName "mappend")
                        (VarE $ mkName concept))
                      (AppE
                        (VarE $ mkName "ref")
                        (VarE $ defLabelName))
                )
                [] -- No wheres
            ]


labelDef :: String -> [Dec]
labelDef concept = [sig, fun]
  where
    name = mkName $ concept ++ "DefinitionLabel"
    sig = SigD
            name
            (ConT $ mkName "Label")
    fun = FunD
            name
            [
              Clause
                [] -- No arguments
                (
                  NormalB $
                    AppE
                      (AppE
                        (ConE $ mkName "Label")
                        (ConE $ mkName "Definition"))
                      (LitE $ StringL concept)
                )
                [] -- No wheres
            ]
