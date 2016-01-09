module TH.MetaLabel (
      makeMakeLabel
    , makeMakeLabels
    ) where

import           Types
import           Utils

import           Prelude

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (sequenceQ)


makeMakeLabels :: [(String, String)] -> Q [Dec]
makeMakeLabels ns = fmap concat $ sequenceQ $ map makeMakeLabel ns

makeMakeLabel :: (String, String) -> Q [Dec]
makeMakeLabel (short, labelName) = return [makeLabelSig, makeLabelFun, makeLabelsSig, makeLabelsFun]
  where
    funNameStr :: String
    funNameStr = "make" ++ pascalCase short

    funName :: Name
    funName = mkName funNameStr

    funsName :: Name
    funsName = mkName $ funNameStr ++ "s"

    makeLabelSig :: Dec
    makeLabelSig = SigD funName
                    $ AppT
                        (AppT
                          ArrowT
                          (ConT ''String))
                        (ConT ''DecsQ)


    makeLabelFun :: Dec
    makeLabelFun = FunD funName
                [
                  Clause
                    []
                    (NormalB $
                      AppE
                        (VarE $ mkName "makeLabel")
                        -- (AppE
                            -- (VarE 'mkName)
                            (LitE $ StringL $ labelName))
                    []
                ]

    makeLabelsSig :: Dec
    makeLabelsSig = SigD funsName
                    $ AppT
                        (AppT
                          ArrowT
                          (AppT
                            ListT
                            (ConT ''String)))
                        (ConT ''DecsQ)

    makeLabelsFun :: Dec
    makeLabelsFun = FunD funsName
                [
                  Clause
                    []
                    (NormalB $
                      AppE
                        (VarE $ mkName "makeLabels")
                        -- (AppE
                            -- (VarE 'mkName)
                            (LitE $ StringL $ labelName))
                    []
                ]
