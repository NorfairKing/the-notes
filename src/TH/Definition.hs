module TH.Definition (
      makeDef
    ) where

import           Types

import           Prelude             (return)

import           Language.Haskell.TH


makeDef :: String -> Q [Dec]
makeDef str = return (indexDef str)

indexDef :: String -> [Dec]
indexDef concept = [sig, fun]
  where
    name = mkName concept
    sig  = SigD
            name
            (ConT $ mkName "Note")
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

