module TH.Label where

import           Types
import           Utils

import           Prelude

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax (sequenceQ)

import           TH.MetaLabel

makeMakeLabels [
      ("de"     , "Definition"  )
    , ("thm"    , "Theorem"     )
    , ("pro"    , "Proposition" )
    , ("prop"   , "Property"    )
    , ("ex"     , "Example"     )
    , ("fig"    , "Figure"      )
    , ("nte"    , "Note"        )
    ]

makeLabels :: String -> [String] -> Q [Dec]
makeLabels n strs = fmap concat $ sequenceQ $ map (makeLabel n) strs

makeLabel :: String -> String -> Q [Dec]
makeLabel labelConsName concept = return [labelSig, labelFun]
  where
    funName :: Name
    funName = mkName . (++ labelConsName ++ "Label") . camelCase . sanitize $ concept

    labelName :: String
    labelName = kebabCase $ sanitize concept

    labelSig :: Dec
    labelSig = SigD funName (ConT ''Label)

    labelNameRef :: Name
    labelNameRef = mkName labelConsName

    labelFun :: Dec
    labelFun = FunD funName
                [
                  Clause
                    []
                    (NormalB $
                      AppE
                        (AppE
                          (ConE 'MkLabel)
                          (ConE labelNameRef))
                        (LitE $ StringL $ labelName))
                    []
                ]
